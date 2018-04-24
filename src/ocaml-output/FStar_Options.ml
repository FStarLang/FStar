open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string [@@deriving show]
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Low -> true | uu____11 -> false
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Medium -> true | uu____17 -> false
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | High -> true | uu____23 -> false
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Extreme -> true | uu____29 -> false
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Other _0 -> true | uu____36 -> false
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee -> match projectee with | Other _0 -> _0
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset [@@deriving show]
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu____77 -> false
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | String _0 -> true | uu____91 -> false
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | Path _0 -> true | uu____105 -> false
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | Path _0 -> _0
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu____119 -> false
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | List _0 -> true | uu____135 -> false
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee -> match projectee with | List _0 -> _0
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Unset -> true | uu____154 -> false
let (mk_bool : Prims.bool -> option_val) = fun _0_4 -> Bool _0_4
let (mk_string : Prims.string -> option_val) = fun _0_5 -> String _0_5
let (mk_path : Prims.string -> option_val) = fun _0_6 -> Path _0_6
let (mk_int : Prims.int -> option_val) = fun _0_7 -> Int _0_7
let (mk_list : option_val Prims.list -> option_val) = fun _0_8 -> List _0_8
type options =
  | Set 
  | Reset 
  | Restore [@@deriving show]
let (uu___is_Set : options -> Prims.bool) =
  fun projectee -> match projectee with | Set -> true | uu____182 -> false
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee -> match projectee with | Reset -> true | uu____188 -> false
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee ->
    match projectee with | Restore -> true | uu____194 -> false
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (__unit_tests : unit -> Prims.bool) =
  fun uu____236 -> FStar_ST.op_Bang __unit_tests__
let (__set_unit_tests : unit -> unit) =
  fun uu____270 -> FStar_ST.op_Colon_Equals __unit_tests__ true
let (__clear_unit_tests : unit -> unit) =
  fun uu____304 -> FStar_ST.op_Colon_Equals __unit_tests__ false
let (as_bool : option_val -> Prims.bool) =
  fun uu___41_338 ->
    match uu___41_338 with
    | Bool b -> b
    | uu____340 -> failwith "Impos: expected Bool"
let (as_int : option_val -> Prims.int) =
  fun uu___42_345 ->
    match uu___42_345 with
    | Int b -> b
    | uu____347 -> failwith "Impos: expected Int"
let (as_string : option_val -> Prims.string) =
  fun uu___43_352 ->
    match uu___43_352 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____355 -> failwith "Impos: expected String"
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___44_362 ->
    match uu___44_362 with
    | List ts -> ts
    | uu____368 -> failwith "Impos: expected List"
let as_list :
  'Auu____377 .
    (option_val -> 'Auu____377) -> option_val -> 'Auu____377 Prims.list
  =
  fun as_t ->
    fun x ->
      let uu____395 = as_list' x in
      FStar_All.pipe_right uu____395 (FStar_List.map as_t)
let as_option :
  'Auu____408 .
    (option_val -> 'Auu____408) ->
      option_val -> 'Auu____408 FStar_Pervasives_Native.option
  =
  fun as_t ->
    fun uu___45_423 ->
      match uu___45_423 with
      | Unset -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____427 = as_t v1 in FStar_Pervasives_Native.Some uu____427
type optionstate = option_val FStar_Util.smap[@@deriving show]
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (peek : unit -> optionstate) =
  fun uu____475 ->
    let uu____476 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____476
let (pop : unit -> unit) =
  fun uu____516 ->
    let uu____517 = FStar_ST.op_Bang fstar_options in
    match uu____517 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____553::[] -> failwith "TOO MANY POPS!"
    | uu____554::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let (push : unit -> unit) =
  fun uu____595 ->
    let uu____596 =
      let uu____599 =
        let uu____602 = peek () in FStar_Util.smap_copy uu____602 in
      let uu____605 = FStar_ST.op_Bang fstar_options in uu____599 ::
        uu____605 in
    FStar_ST.op_Colon_Equals fstar_options uu____596
let (set : optionstate -> unit) =
  fun o ->
    let uu____683 = FStar_ST.op_Bang fstar_options in
    match uu____683 with
    | [] -> failwith "set on empty option stack"
    | uu____719::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let (set_option : Prims.string -> option_val -> unit) =
  fun k ->
    fun v1 -> let uu____766 = peek () in FStar_Util.smap_add uu____766 k v1
let (set_option' :
  (Prims.string, option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____777 -> match uu____777 with | (k, v1) -> set_option k v1
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f -> push (); (let retv = f () in pop (); retv)
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (add_light_off_file : Prims.string -> unit) =
  fun filename ->
    let uu____848 =
      let uu____851 = FStar_ST.op_Bang light_off_files in filename ::
        uu____851 in
    FStar_ST.op_Colon_Equals light_off_files uu____848
let (defaults :
  (Prims.string, option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
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
  ("expose_interfaces", (Bool false));
  ("extract", Unset);
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("fstar_home", Unset);
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
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int (Prims.parse_int "0")));
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
  ("use_two_phase_tc", (Bool false));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))]
let (init : unit -> unit) =
  fun uu____1310 ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let (clear : unit -> unit) =
  fun uu____1327 ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let (_run : unit) = clear ()
let (get_option : Prims.string -> option_val) =
  fun s ->
    let uu____1408 =
      let uu____1411 = peek () in FStar_Util.smap_try_find uu____1411 s in
    match uu____1408 with
    | FStar_Pervasives_Native.None ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt :
  'Auu____1421 . Prims.string -> (option_val -> 'Auu____1421) -> 'Auu____1421
  = fun s -> fun c -> let uu____1437 = get_option s in c uu____1437
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1442 -> lookup_opt "admit_smt_queries" as_bool
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1449 -> lookup_opt "admit_except" (as_option as_string)
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1456 -> lookup_opt "cache_checked_modules" as_bool
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1463 -> lookup_opt "cache_dir" (as_option as_string)
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1472 -> lookup_opt "codegen" (as_option as_string)
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1481 -> lookup_opt "codegen-lib" (as_list as_string)
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1490 -> lookup_opt "debug" (as_list as_string)
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1499 -> lookup_opt "debug_level" (as_list as_string)
let (get_defensive : unit -> Prims.string) =
  fun uu____1506 -> lookup_opt "defensive" as_string
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1513 -> lookup_opt "dep" (as_option as_string)
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1520 -> lookup_opt "detail_errors" as_bool
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1525 -> lookup_opt "detail_hint_replay" as_bool
let (get_doc : unit -> Prims.bool) =
  fun uu____1530 -> lookup_opt "doc" as_bool
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1537 -> lookup_opt "dump_module" (as_list as_string)
let (get_eager_inference : unit -> Prims.bool) =
  fun uu____1544 -> lookup_opt "eager_inference" as_bool
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1549 -> lookup_opt "expose_interfaces" as_bool
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1558 -> lookup_opt "extract" (as_option (as_list as_string))
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1571 -> lookup_opt "extract_module" (as_list as_string)
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1580 -> lookup_opt "extract_namespace" (as_list as_string)
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1587 -> lookup_opt "fs_typ_app" as_bool
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1594 -> lookup_opt "fstar_home" (as_option as_string)
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1601 -> lookup_opt "hide_uvar_nums" as_bool
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1606 -> lookup_opt "hint_info" as_bool
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1613 -> lookup_opt "hint_file" (as_option as_string)
let (get_in : unit -> Prims.bool) = fun uu____1620 -> lookup_opt "in" as_bool
let (get_ide : unit -> Prims.bool) =
  fun uu____1625 -> lookup_opt "ide" as_bool
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1632 -> lookup_opt "include" (as_list as_string)
let (get_indent : unit -> Prims.bool) =
  fun uu____1639 -> lookup_opt "indent" as_bool
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1644 -> lookup_opt "initial_fuel" as_int
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1649 -> lookup_opt "initial_ifuel" as_int
let (get_lax : unit -> Prims.bool) =
  fun uu____1654 -> lookup_opt "lax" as_bool
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1661 -> lookup_opt "load" (as_list as_string)
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1668 -> lookup_opt "log_queries" as_bool
let (get_log_types : unit -> Prims.bool) =
  fun uu____1673 -> lookup_opt "log_types" as_bool
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1678 -> lookup_opt "max_fuel" as_int
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1683 -> lookup_opt "max_ifuel" as_int
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1688 -> lookup_opt "min_fuel" as_int
let (get_MLish : unit -> Prims.bool) =
  fun uu____1693 -> lookup_opt "MLish" as_bool
let (get_n_cores : unit -> Prims.int) =
  fun uu____1698 -> lookup_opt "n_cores" as_int
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1703 -> lookup_opt "no_default_includes" as_bool
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1710 -> lookup_opt "no_extract" (as_list as_string)
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1717 -> lookup_opt "no_location_info" as_bool
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1722 -> lookup_opt "no_smt" as_bool
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1727 -> lookup_opt "normalize_pure_terms_for_extraction" as_bool
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1734 -> lookup_opt "odir" (as_option as_string)
let (get_ugly : unit -> Prims.bool) =
  fun uu____1741 -> lookup_opt "ugly" as_bool
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1748 -> lookup_opt "prims" (as_option as_string)
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1755 -> lookup_opt "print_bound_var_types" as_bool
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1760 -> lookup_opt "print_effect_args" as_bool
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1765 -> lookup_opt "print_full_names" as_bool
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1770 -> lookup_opt "print_implicits" as_bool
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1775 -> lookup_opt "print_universes" as_bool
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1780 -> lookup_opt "print_z3_statistics" as_bool
let (get_prn : unit -> Prims.bool) =
  fun uu____1785 -> lookup_opt "prn" as_bool
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1790 -> lookup_opt "query_stats" as_bool
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1795 -> lookup_opt "record_hints" as_bool
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1802 -> lookup_opt "reuse_hint_for" (as_option as_string)
let (get_silent : unit -> Prims.bool) =
  fun uu____1809 -> lookup_opt "silent" as_bool
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1816 -> lookup_opt "smt" (as_option as_string)
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1823 -> lookup_opt "smtencoding.elim_box" as_bool
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1828 -> lookup_opt "smtencoding.nl_arith_repr" as_string
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1833 -> lookup_opt "smtencoding.l_arith_repr" as_string
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1838 -> lookup_opt "tactic_raw_binders" as_bool
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1843 -> lookup_opt "tactic_trace" as_bool
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1848 -> lookup_opt "tactic_trace_d" as_int
let (get_timing : unit -> Prims.bool) =
  fun uu____1853 -> lookup_opt "timing" as_bool
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1858 -> lookup_opt "trace_error" as_bool
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1863 -> lookup_opt "unthrottle_inductives" as_bool
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1868 -> lookup_opt "unsafe_tactic_exec" as_bool
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1873 -> lookup_opt "use_eq_at_higher_order" as_bool
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1878 -> lookup_opt "use_hints" as_bool
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1883 -> lookup_opt "use_hint_hashes" as_bool
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1890 -> lookup_opt "use_native_tactics" (as_option as_string)
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1897 ->
    let uu____1898 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1898
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1907 ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1920 ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1929 -> lookup_opt "verify_module" (as_list as_string)
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1938 -> lookup_opt "__temp_no_proj" (as_list as_string)
let (get_version : unit -> Prims.bool) =
  fun uu____1945 -> lookup_opt "version" as_bool
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1950 -> lookup_opt "warn_default_effects" as_bool
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1957 -> lookup_opt "z3cliopt" (as_list as_string)
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1964 -> lookup_opt "z3refresh" as_bool
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1969 -> lookup_opt "z3rlimit" as_int
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1974 -> lookup_opt "z3rlimit_factor" as_int
let (get_z3seed : unit -> Prims.int) =
  fun uu____1979 -> lookup_opt "z3seed" as_int
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1984 -> lookup_opt "use_two_phase_tc" as_bool
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1989 -> lookup_opt "__no_positivity" as_bool
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1994 -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let (get_warn_error : unit -> Prims.string) =
  fun uu____1999 -> lookup_opt "warn_error" as_string
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____2004 -> lookup_opt "use_extracted_interfaces" as_bool
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___46_2009 ->
    match uu___46_2009 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1 ->
    fun l2 ->
      match l1 with
      | Other uu____2021 -> l1 = l2
      | Low -> l1 = l2
      | Medium -> (l2 = Low) || (l2 = Medium)
      | High -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2 ->
    let uu____2027 = get_debug_level () in
    FStar_All.pipe_right uu____2027
      (FStar_Util.for_some (fun l1 -> one_debug_level_geq (dlevel l1) l2))
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"]
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (display_version : unit -> unit) =
  fun uu____2400 ->
    let uu____2401 =
      let uu____2402 = FStar_ST.op_Bang _version in
      let uu____2432 = FStar_ST.op_Bang _platform in
      let uu____2462 = FStar_ST.op_Bang _compiler in
      let uu____2492 = FStar_ST.op_Bang _date in
      let uu____2522 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2402
        uu____2432 uu____2462 uu____2492 uu____2522 in
    FStar_Util.print_string uu____2401
let display_usage_aux :
  'Auu____2558 'Auu____2559 .
    ('Auu____2558, Prims.string, 'Auu____2559 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2607 ->
         match uu____2607 with
         | (uu____2618, flag, p, doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2630 =
                      let uu____2631 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2631 in
                    FStar_Util.print_string uu____2630
                  else
                    (let uu____2633 =
                       let uu____2634 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2634 doc in
                     FStar_Util.print_string uu____2633)
              | FStar_Getopt.OneArg (uu____2635, argname) ->
                  if doc = ""
                  then
                    let uu____2643 =
                      let uu____2644 = FStar_Util.colorize_bold flag in
                      let uu____2645 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2644 uu____2645 in
                    FStar_Util.print_string uu____2643
                  else
                    (let uu____2647 =
                       let uu____2648 = FStar_Util.colorize_bold flag in
                       let uu____2649 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2648
                         uu____2649 doc in
                     FStar_Util.print_string uu____2647))) specs
let (mk_spec :
  (FStar_BaseTypes.char, Prims.string, option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o ->
    let uu____2675 = o in
    match uu____2675 with
    | (ns, name, arg, desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2708 =
                let uu____2709 = f () in set_option name uu____2709 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f, d) ->
              let g x = let uu____2724 = f x in set_option name uu____2724 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let prev_values =
        let uu____2743 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2743 in
      mk_list (value :: prev_values)
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let uu____2766 =
        let uu____2769 = lookup_opt name as_list' in
        FStar_List.append uu____2769 [value] in
      mk_list uu____2766
let accumulate_string :
  'Auu____2782 .
    Prims.string -> ('Auu____2782 -> Prims.string) -> 'Auu____2782 -> unit
  =
  fun name ->
    fun post_processor ->
      fun value ->
        let uu____2803 =
          let uu____2804 =
            let uu____2805 = post_processor value in mk_string uu____2805 in
          accumulated_option name uu____2804 in
        set_option name uu____2803
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
[@@deriving show]
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____2901 -> false
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | IntStr _0 -> true | uu____2915 -> false
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | IntStr _0 -> _0
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | BoolStr -> true | uu____2928 -> false
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PathStr _0 -> true | uu____2935 -> false
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | PathStr _0 -> _0
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleStr _0 -> true | uu____2949 -> false
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | SimpleStr _0 -> _0
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | EnumStr _0 -> true | uu____2965 -> false
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee -> match projectee with | EnumStr _0 -> _0
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | OpenEnumStr _0 -> true | uu____2991 -> false
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | OpenEnumStr _0 -> _0
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PostProcessed _0 -> true | uu____3030 -> false
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val, opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | PostProcessed _0 -> _0
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Accumulated _0 -> true | uu____3065 -> false
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | Accumulated _0 -> _0
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____3079 -> false
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | ReverseAccumulated _0 -> _0
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | WithSideEffect _0 -> true | uu____3100 -> false
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit, opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidArgument uu____3138 -> true
    | uu____3139 -> false
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidArgument uu____3146 -> uu____3146
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name ->
    fun typ ->
      fun str_val ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____3166 ->
              let uu____3167 = FStar_Util.safe_int_of_string str_val in
              (match uu____3167 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr ->
              let uu____3171 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____3171
          | PathStr uu____3174 -> mk_path str_val
          | SimpleStr uu____3175 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____3180 -> mk_string str_val
          | PostProcessed (pp, elem_spec) ->
              let uu____3195 = parse_opt_val opt_name elem_spec str_val in
              pp uu____3195
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect, elem_spec) ->
              (side_effect (); parse_opt_val opt_name elem_spec str_val)
        with
        | InvalidArgument opt_name1 ->
            let uu____3214 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____3214
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
    | PostProcessed (uu____3251, elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____3261, elem_spec) -> desc_of_opt_type elem_spec
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name ->
    fun typ ->
      let parser = parse_opt_val opt_name typ in
      let uu____3288 = desc_of_opt_type typ in
      match uu____3288 with
      | FStar_Pervasives_Native.None ->
          FStar_Getopt.ZeroArgs ((fun uu____3294 -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let (pp_validate_dir : option_val -> option_val) =
  fun p -> let pp = as_string p in FStar_Util.mkdir false pp; p
let (pp_lowercase : option_val -> option_val) =
  fun s ->
    let uu____3311 =
      let uu____3312 = as_string s in FStar_String.lowercase uu____3312 in
    mk_string uu____3311
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char, Prims.string, opt_type, Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____3333 ->
    let uu____3344 =
      let uu____3355 =
        let uu____3366 =
          let uu____3375 = let uu____3376 = mk_bool true in Const uu____3376 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____3375,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____3377 =
          let uu____3388 =
            let uu____3399 =
              let uu____3410 =
                let uu____3421 =
                  let uu____3432 =
                    let uu____3443 =
                      let uu____3454 =
                        let uu____3465 =
                          let uu____3474 =
                            let uu____3475 = mk_bool true in Const uu____3475 in
                          (FStar_Getopt.noshort, "detail_errors", uu____3474,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                        let uu____3476 =
                          let uu____3487 =
                            let uu____3496 =
                              let uu____3497 = mk_bool true in
                              Const uu____3497 in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3496,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                          let uu____3498 =
                            let uu____3509 =
                              let uu____3518 =
                                let uu____3519 = mk_bool true in
                                Const uu____3519 in
                              (FStar_Getopt.noshort, "doc", uu____3518,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                            let uu____3520 =
                              let uu____3531 =
                                let uu____3542 =
                                  let uu____3551 =
                                    let uu____3552 = mk_bool true in
                                    Const uu____3552 in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____3551,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                                let uu____3553 =
                                  let uu____3564 =
                                    let uu____3575 =
                                      let uu____3586 =
                                        let uu____3597 =
                                          let uu____3606 =
                                            let uu____3607 = mk_bool true in
                                            Const uu____3607 in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____3606,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                        let uu____3608 =
                                          let uu____3619 =
                                            let uu____3630 =
                                              let uu____3639 =
                                                let uu____3640 = mk_bool true in
                                                Const uu____3640 in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____3639,
                                                "Don't print unification variable numbers") in
                                            let uu____3641 =
                                              let uu____3652 =
                                                let uu____3663 =
                                                  let uu____3672 =
                                                    let uu____3673 =
                                                      mk_bool true in
                                                    Const uu____3673 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____3672,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                let uu____3674 =
                                                  let uu____3685 =
                                                    let uu____3694 =
                                                      let uu____3695 =
                                                        mk_bool true in
                                                      Const uu____3695 in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____3694,
                                                      "Legacy interactive mode; reads input from stdin") in
                                                  let uu____3696 =
                                                    let uu____3707 =
                                                      let uu____3716 =
                                                        let uu____3717 =
                                                          mk_bool true in
                                                        Const uu____3717 in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____3716,
                                                        "JSON-based interactive mode for IDEs") in
                                                    let uu____3718 =
                                                      let uu____3729 =
                                                        let uu____3740 =
                                                          let uu____3749 =
                                                            let uu____3750 =
                                                              mk_bool true in
                                                            Const uu____3750 in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____3749,
                                                            "Parses and outputs the files on the command line") in
                                                        let uu____3751 =
                                                          let uu____3762 =
                                                            let uu____3773 =
                                                              let uu____3784
                                                                =
                                                                let uu____3793
                                                                  =
                                                                  let uu____3794
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____3794 in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____3793,
                                                                  "Run the lax-type checker only (admit all verification conditions)") in
                                                              let uu____3795
                                                                =
                                                                let uu____3806
                                                                  =
                                                                  let uu____3817
                                                                    =
                                                                    let uu____3826
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3827 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3826,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                  let uu____3828
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    let uu____3848
                                                                    =
                                                                    let uu____3849
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3849 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3848,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3861
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3894
                                                                    =
                                                                    let uu____3903
                                                                    =
                                                                    let uu____3904
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3904 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3903,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3905
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3927
                                                                    =
                                                                    let uu____3936
                                                                    =
                                                                    let uu____3937
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3937 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3936,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3949
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3969
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3970 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3969,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3971
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    let uu____3992
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3992 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3991,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead") in
                                                                    let uu____3993
                                                                    =
                                                                    let uu____4004
                                                                    =
                                                                    let uu____4013
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4014 in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____4013,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.") in
                                                                    let uu____4015
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    let uu____4037
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4057
                                                                    =
                                                                    let uu____4058
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4058 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____4057,
                                                                    "Print the types of bound variables") in
                                                                    let uu____4059
                                                                    =
                                                                    let uu____4070
                                                                    =
                                                                    let uu____4079
                                                                    =
                                                                    let uu____4080
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4080 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____4079,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____4081
                                                                    =
                                                                    let uu____4092
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    let uu____4102
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4102 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____4101,
                                                                    "Print full names of variables") in
                                                                    let uu____4103
                                                                    =
                                                                    let uu____4114
                                                                    =
                                                                    let uu____4123
                                                                    =
                                                                    let uu____4124
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4124 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____4123,
                                                                    "Print implicit arguments") in
                                                                    let uu____4125
                                                                    =
                                                                    let uu____4136
                                                                    =
                                                                    let uu____4145
                                                                    =
                                                                    let uu____4146
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4146 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____4145,
                                                                    "Print universes") in
                                                                    let uu____4147
                                                                    =
                                                                    let uu____4158
                                                                    =
                                                                    let uu____4167
                                                                    =
                                                                    let uu____4168
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4168 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____4167,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____4169
                                                                    =
                                                                    let uu____4180
                                                                    =
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4190
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4190 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4189,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____4191
                                                                    =
                                                                    let uu____4202
                                                                    =
                                                                    let uu____4211
                                                                    =
                                                                    let uu____4212
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4212 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4211,
                                                                    "Print SMT query statistics") in
                                                                    let uu____4213
                                                                    =
                                                                    let uu____4224
                                                                    =
                                                                    let uu____4233
                                                                    =
                                                                    let uu____4234
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4234 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4233,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____4235
                                                                    =
                                                                    let uu____4246
                                                                    =
                                                                    let uu____4257
                                                                    =
                                                                    let uu____4266
                                                                    =
                                                                    let uu____4267
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4267 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4266,
                                                                    " ") in
                                                                    let uu____4268
                                                                    =
                                                                    let uu____4279
                                                                    =
                                                                    let uu____4290
                                                                    =
                                                                    let uu____4301
                                                                    =
                                                                    let uu____4312
                                                                    =
                                                                    let uu____4323
                                                                    =
                                                                    let uu____4332
                                                                    =
                                                                    let uu____4333
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4333 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4332,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____4334
                                                                    =
                                                                    let uu____4345
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    let uu____4355
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4355 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4354,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____4356
                                                                    =
                                                                    let uu____4367
                                                                    =
                                                                    let uu____4378
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    let uu____4388
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4388 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4387,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4400
                                                                    =
                                                                    let uu____4409
                                                                    =
                                                                    let uu____4410
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4410 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4409,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____4411
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    let uu____4431
                                                                    =
                                                                    let uu____4432
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4432 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4431,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____4433
                                                                    =
                                                                    let uu____4444
                                                                    =
                                                                    let uu____4453
                                                                    =
                                                                    let uu____4454
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4454 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4453,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____4455
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4476
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4476 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4475,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____4477
                                                                    =
                                                                    let uu____4488
                                                                    =
                                                                    let uu____4497
                                                                    =
                                                                    let uu____4498
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4498 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4497,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____4499
                                                                    =
                                                                    let uu____4510
                                                                    =
                                                                    let uu____4519
                                                                    =
                                                                    let uu____4520
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4520 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4519,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4532
                                                                    =
                                                                    let uu____4541
                                                                    =
                                                                    let uu____4542
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4542 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4541,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____4543
                                                                    =
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4565
                                                                    =
                                                                    let uu____4574
                                                                    =
                                                                    let uu____4575
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4575 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4574,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4576
                                                                    =
                                                                    let uu____4587
                                                                    =
                                                                    let uu____4598
                                                                    =
                                                                    let uu____4609
                                                                    =
                                                                    let uu____4620
                                                                    =
                                                                    let uu____4629
                                                                    =
                                                                    let uu____4630
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4630 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4629,
                                                                    "Don't use this option yet") in
                                                                    let uu____4631
                                                                    =
                                                                    let uu____4642
                                                                    =
                                                                    let uu____4652
                                                                    =
                                                                    let uu____4653
                                                                    =
                                                                    let uu____4661
                                                                    =
                                                                    let uu____4662
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4662 in
                                                                    ((fun
                                                                    uu____4668
                                                                    ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4661) in
                                                                    WithSideEffect
                                                                    uu____4653 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4652,
                                                                    "Display version number") in
                                                                    let uu____4672
                                                                    =
                                                                    let uu____4684
                                                                    =
                                                                    let uu____4693
                                                                    =
                                                                    let uu____4694
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4694 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4693,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4695
                                                                    =
                                                                    let uu____4706
                                                                    =
                                                                    let uu____4717
                                                                    =
                                                                    let uu____4726
                                                                    =
                                                                    let uu____4727
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4727 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4726,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4728
                                                                    =
                                                                    let uu____4739
                                                                    =
                                                                    let uu____4750
                                                                    =
                                                                    let uu____4761
                                                                    =
                                                                    let uu____4772
                                                                    =
                                                                    let uu____4783
                                                                    =
                                                                    let uu____4792
                                                                    =
                                                                    let uu____4793
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4793 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4792,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4794
                                                                    =
                                                                    let uu____4805
                                                                    =
                                                                    let uu____4814
                                                                    =
                                                                    let uu____4815
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4815 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4814,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4816
                                                                    =
                                                                    let uu____4827
                                                                    =
                                                                    let uu____4838
                                                                    =
                                                                    let uu____4847
                                                                    =
                                                                    let uu____4848
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4848 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____4847,
                                                                    "Extract interfaces from the dependencies and use them for verification") in
                                                                    let uu____4849
                                                                    =
                                                                    let uu____4860
                                                                    =
                                                                    let uu____4870
                                                                    =
                                                                    let uu____4871
                                                                    =
                                                                    let uu____4879
                                                                    =
                                                                    let uu____4880
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4880 in
                                                                    ((fun
                                                                    uu____4886
                                                                    ->
                                                                    (
                                                                    let uu____4888
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4888);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4879) in
                                                                    WithSideEffect
                                                                    uu____4871 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4870,
                                                                    "Display this information") in
                                                                    [uu____4860] in
                                                                    uu____4838
                                                                    ::
                                                                    uu____4849 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4827 in
                                                                    uu____4805
                                                                    ::
                                                                    uu____4816 in
                                                                    uu____4783
                                                                    ::
                                                                    uu____4794 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4772 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4761 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4750 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4739 in
                                                                    uu____4717
                                                                    ::
                                                                    uu____4728 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4706 in
                                                                    uu____4684
                                                                    ::
                                                                    uu____4695 in
                                                                    uu____4642
                                                                    ::
                                                                    uu____4672 in
                                                                    uu____4620
                                                                    ::
                                                                    uu____4631 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4609 in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4598 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4587 in
                                                                    uu____4565
                                                                    ::
                                                                    uu____4576 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4554 in
                                                                    uu____4532
                                                                    ::
                                                                    uu____4543 in
                                                                    uu____4510
                                                                    ::
                                                                    uu____4521 in
                                                                    uu____4488
                                                                    ::
                                                                    uu____4499 in
                                                                    uu____4466
                                                                    ::
                                                                    uu____4477 in
                                                                    uu____4444
                                                                    ::
                                                                    uu____4455 in
                                                                    uu____4422
                                                                    ::
                                                                    uu____4433 in
                                                                    uu____4400
                                                                    ::
                                                                    uu____4411 in
                                                                    uu____4378
                                                                    ::
                                                                    uu____4389 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4367 in
                                                                    uu____4345
                                                                    ::
                                                                    uu____4356 in
                                                                    uu____4323
                                                                    ::
                                                                    uu____4334 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4312 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4301 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4290 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4279 in
                                                                    uu____4257
                                                                    ::
                                                                    uu____4268 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4246 in
                                                                    uu____4224
                                                                    ::
                                                                    uu____4235 in
                                                                    uu____4202
                                                                    ::
                                                                    uu____4213 in
                                                                    uu____4180
                                                                    ::
                                                                    uu____4191 in
                                                                    uu____4158
                                                                    ::
                                                                    uu____4169 in
                                                                    uu____4136
                                                                    ::
                                                                    uu____4147 in
                                                                    uu____4114
                                                                    ::
                                                                    uu____4125 in
                                                                    uu____4092
                                                                    ::
                                                                    uu____4103 in
                                                                    uu____4070
                                                                    ::
                                                                    uu____4081 in
                                                                    uu____4048
                                                                    ::
                                                                    uu____4059 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____4037 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____4026 in
                                                                    uu____4004
                                                                    ::
                                                                    uu____4015 in
                                                                    uu____3982
                                                                    ::
                                                                    uu____3993 in
                                                                    uu____3960
                                                                    ::
                                                                    uu____3971 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3949 in
                                                                    uu____3927
                                                                    ::
                                                                    uu____3938 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3916 in
                                                                    uu____3894
                                                                    ::
                                                                    uu____3905 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3883 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3872 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3861 in
                                                                    uu____3839
                                                                    ::
                                                                    uu____3850 in
                                                                  uu____3817
                                                                    ::
                                                                    uu____3828 in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____3806 in
                                                              uu____3784 ::
                                                                uu____3795 in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____3773 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____3762 in
                                                        uu____3740 ::
                                                          uu____3751 in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____3729 in
                                                    uu____3707 :: uu____3718 in
                                                  uu____3685 :: uu____3696 in
                                                uu____3663 :: uu____3674 in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____3652 in
                                            uu____3630 :: uu____3641 in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____3619 in
                                        uu____3597 :: uu____3608 in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____3586 in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____3575 in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____3564 in
                                uu____3542 :: uu____3553 in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____3531 in
                            uu____3509 :: uu____3520 in
                          uu____3487 :: uu____3498 in
                        uu____3465 :: uu____3476 in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3454 in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____3443 in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____3432 in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____3421 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____3410 in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____3399 in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____3388 in
        uu____3366 :: uu____3377 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____3355 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____3344
and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5648 ->
    let uu____5651 = specs_with_types () in
    FStar_List.map
      (fun uu____5676 ->
         match uu____5676 with
         | (short, long, typ, doc) ->
             let uu____5689 =
               let uu____5700 = arg_spec_of_opt_type long typ in
               (short, long, uu____5700, doc) in
             mk_spec uu____5689) uu____5651
let (settable : Prims.string -> Prims.bool) =
  fun uu___47_5709 ->
    match uu___47_5709 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
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
    | "no_tactics" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "tactic_raw_binders" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____5710 -> false
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
       (fun uu____5769 ->
          match uu____5769 with
          | (uu____5780, x, uu____5782, uu____5783) -> settable x))
let (resettable_specs :
  (FStar_BaseTypes.char, Prims.string, unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5829 ->
          match uu____5829 with
          | (uu____5840, x, uu____5842, uu____5843) -> resettable x))
let (display_usage : unit -> unit) =
  fun uu____5852 -> let uu____5853 = specs () in display_usage_aux uu____5853
let (fstar_home : unit -> Prims.string) =
  fun uu____5870 ->
    let uu____5871 = get_fstar_home () in
    match uu____5871 with
    | FStar_Pervasives_Native.None ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5877 =
            let uu____5882 = mk_string x1 in ("fstar_home", uu____5882) in
          set_option' uu____5877);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | File_argument uu____5893 -> true
    | uu____5894 -> false
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | File_argument uu____5901 -> uu____5901
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
        if s = ""
        then FStar_Getopt.Success
        else
          FStar_Getopt.parse_string specs1
            (fun s1 -> FStar_Exn.raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____5949 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5949
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res, Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6001 ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i ->
           let uu____6006 =
             let uu____6009 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____6009 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____6006) in
    let uu____6078 =
      let uu____6081 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6081 in
    (res, uu____6078)
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6125 -> FStar_ST.op_Bang file_list_
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____6170 = specs () in
       FStar_Getopt.parse_cmdline uu____6170 (fun x -> ()) in
     (let uu____6176 =
        let uu____6181 =
          let uu____6182 = FStar_List.map mk_string old_verify_module in
          List uu____6182 in
        ("verify_module", uu____6181) in
      set_option' uu____6176);
     r)
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____6192 =
        let uu____6193 =
          let uu____6194 =
            let uu____6195 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____6195 in
          (FStar_String.length f1) - uu____6194 in
        uu____6193 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6192 in
    FStar_String.lowercase f2
let (should_verify : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6201 = get_lax () in
    if uu____6201
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn ->
    let uu____6211 = module_name_of_file_name fn in should_verify uu____6211
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6217 = get___temp_no_proj () in
    FStar_List.contains m uu____6217
let (should_print_message : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6225 = should_verify m in
    if uu____6225 then m <> "Prims" else false
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6233 ->
    let uu____6234 = get_no_default_includes () in
    if uu____6234
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____6242 =
         let uu____6245 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____6245
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____6258 =
         let uu____6261 = get_include () in
         FStar_List.append uu____6261 ["."] in
       FStar_List.append uu____6242 uu____6258)
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename ->
    let uu____6271 = FStar_Util.is_path_absolute filename in
    if uu____6271
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____6278 =
         let uu____6281 = include_path () in FStar_List.rev uu____6281 in
       FStar_Util.find_map uu____6278
         (fun p ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let (prims : unit -> Prims.string) =
  fun uu____6296 ->
    let uu____6297 = get_prims () in
    match uu____6297 with
    | FStar_Pervasives_Native.None ->
        let filename = "prims.fst" in
        let uu____6301 = find_file filename in
        (match uu____6301 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None ->
             let uu____6305 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____6305)
    | FStar_Pervasives_Native.Some x -> x
let (prims_basename : unit -> Prims.string) =
  fun uu____6311 ->
    let uu____6312 = prims () in FStar_Util.basename uu____6312
let (pervasives : unit -> Prims.string) =
  fun uu____6317 ->
    let filename = "FStar.Pervasives.fst" in
    let uu____6319 = find_file filename in
    match uu____6319 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None ->
        let uu____6323 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____6323
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6328 ->
    let uu____6329 = pervasives () in FStar_Util.basename uu____6329
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6334 ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____6336 = find_file filename in
    match uu____6336 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None ->
        let uu____6340 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____6340
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname ->
    let uu____6346 = get_odir () in
    match uu____6346 with
    | FStar_Pervasives_Native.None -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath ->
    let uu____6355 = get_cache_dir () in
    match uu____6355 with
    | FStar_Pervasives_Native.None -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6359 = FStar_Util.basename fpath in
        FStar_Util.join_paths x uu____6359
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
             let uu____6413 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____6413 in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s in
           let uu____6417 = FStar_Ident.path_of_text s1 in (uu____6417, true)) in
    let uu____6418 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting))) in
    FStar_All.pipe_right uu____6418 FStar_List.rev
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s ->
    let uu____6488 = get___temp_no_proj () in
    FStar_All.pipe_right uu____6488 (FStar_List.contains s)
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6497 -> lookup_opt "__temp_fast_implicits" as_bool
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6502 -> get_admit_smt_queries ()
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6509 -> get_admit_except ()
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6514 -> get_cache_checked_modules ()
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | OCaml -> true | uu____6520 -> false
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | FSharp -> true | uu____6526 -> false
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Kremlin -> true | uu____6532 -> false
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Plugin -> true | uu____6538 -> false
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6545 ->
    let uu____6546 = get_codegen () in
    FStar_Util.map_opt uu____6546
      (fun uu___48_6550 ->
         match uu___48_6550 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6551 -> failwith "Impossible")
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6560 ->
    let uu____6561 = get_codegen_lib () in
    FStar_All.pipe_right uu____6561
      (FStar_List.map (fun x -> FStar_Util.split x "."))
let (debug_any : unit -> Prims.bool) =
  fun uu____6578 -> let uu____6579 = get_debug () in uu____6579 <> []
let (debug_module : Prims.string -> Prims.bool) =
  fun modul ->
    let uu____6589 = get_debug () in
    FStar_All.pipe_right uu____6589 (FStar_List.contains modul)
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul ->
    fun level ->
      (let uu____6606 = get_debug () in
       FStar_All.pipe_right uu____6606 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let (defensive : unit -> Prims.bool) =
  fun uu____6615 -> let uu____6616 = get_defensive () in uu____6616 <> "no"
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6621 -> let uu____6622 = get_defensive () in uu____6622 = "fail"
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6629 -> get_dep ()
let (detail_errors : unit -> Prims.bool) =
  fun uu____6634 -> get_detail_errors ()
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6639 -> get_detail_hint_replay ()
let (doc : unit -> Prims.bool) = fun uu____6644 -> get_doc ()
let (dump_module : Prims.string -> Prims.bool) =
  fun s ->
    let uu____6650 = get_dump_module () in
    FStar_All.pipe_right uu____6650 (FStar_List.contains s)
let (eager_inference : unit -> Prims.bool) =
  fun uu____6659 -> get_eager_inference ()
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6664 -> get_expose_interfaces ()
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename ->
    let uu____6670 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____6670
let (full_context_dependency : unit -> Prims.bool) = fun uu____6710 -> true
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6715 -> get_hide_uvar_nums ()
let (hint_info : unit -> Prims.bool) =
  fun uu____6720 -> (get_hint_info ()) || (get_query_stats ())
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6727 -> get_hint_file ()
let (ide : unit -> Prims.bool) = fun uu____6732 -> get_ide ()
let (indent : unit -> Prims.bool) = fun uu____6737 -> get_indent ()
let (initial_fuel : unit -> Prims.int) =
  fun uu____6742 ->
    let uu____6743 = get_initial_fuel () in
    let uu____6744 = get_max_fuel () in Prims.min uu____6743 uu____6744
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6749 ->
    let uu____6750 = get_initial_ifuel () in
    let uu____6751 = get_max_ifuel () in Prims.min uu____6750 uu____6751
let (interactive : unit -> Prims.bool) =
  fun uu____6756 -> (get_in ()) || (get_ide ())
let (lax : unit -> Prims.bool) = fun uu____6761 -> get_lax ()
let (load : unit -> Prims.string Prims.list) = fun uu____6768 -> get_load ()
let (legacy_interactive : unit -> Prims.bool) = fun uu____6773 -> get_in ()
let (log_queries : unit -> Prims.bool) = fun uu____6778 -> get_log_queries ()
let (log_types : unit -> Prims.bool) = fun uu____6783 -> get_log_types ()
let (max_fuel : unit -> Prims.int) = fun uu____6788 -> get_max_fuel ()
let (max_ifuel : unit -> Prims.int) = fun uu____6793 -> get_max_ifuel ()
let (min_fuel : unit -> Prims.int) = fun uu____6798 -> get_min_fuel ()
let (ml_ish : unit -> Prims.bool) = fun uu____6803 -> get_MLish ()
let (set_ml_ish : unit -> unit) =
  fun uu____6808 -> set_option "MLish" (Bool true)
let (n_cores : unit -> Prims.int) = fun uu____6813 -> get_n_cores ()
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6818 -> get_no_default_includes ()
let (no_extract : Prims.string -> Prims.bool) =
  fun s ->
    let s1 = FStar_String.lowercase s in
    let uu____6825 = get_no_extract () in
    FStar_All.pipe_right uu____6825
      (FStar_Util.for_some (fun f -> (FStar_String.lowercase f) = s1))
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6836 -> get_normalize_pure_terms_for_extraction ()
let (no_location_info : unit -> Prims.bool) =
  fun uu____6841 -> get_no_location_info ()
let (no_smt : unit -> Prims.bool) = fun uu____6846 -> get_no_smt ()
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6853 -> get_odir ()
let (ugly : unit -> Prims.bool) = fun uu____6858 -> get_ugly ()
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6863 -> get_print_bound_var_types ()
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6868 -> get_print_effect_args ()
let (print_implicits : unit -> Prims.bool) =
  fun uu____6873 -> get_print_implicits ()
let (print_real_names : unit -> Prims.bool) =
  fun uu____6878 -> (get_prn ()) || (get_print_full_names ())
let (print_universes : unit -> Prims.bool) =
  fun uu____6883 -> get_print_universes ()
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6888 -> (get_print_z3_statistics ()) || (get_query_stats ())
let (query_stats : unit -> Prims.bool) = fun uu____6893 -> get_query_stats ()
let (record_hints : unit -> Prims.bool) =
  fun uu____6898 -> get_record_hints ()
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6905 -> get_reuse_hint_for ()
let (silent : unit -> Prims.bool) = fun uu____6910 -> get_silent ()
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6915 -> get_smtencoding_elim_box ()
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6920 ->
    let uu____6921 = get_smtencoding_nl_arith_repr () in
    uu____6921 = "native"
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6926 ->
    let uu____6927 = get_smtencoding_nl_arith_repr () in
    uu____6927 = "wrapped"
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6932 ->
    let uu____6933 = get_smtencoding_nl_arith_repr () in
    uu____6933 = "boxwrap"
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6938 ->
    let uu____6939 = get_smtencoding_l_arith_repr () in uu____6939 = "native"
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6944 ->
    let uu____6945 = get_smtencoding_l_arith_repr () in
    uu____6945 = "boxwrap"
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6950 -> get_tactic_raw_binders ()
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6955 -> get_tactic_trace ()
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6960 -> get_tactic_trace_d ()
let (timing : unit -> Prims.bool) = fun uu____6965 -> get_timing ()
let (trace_error : unit -> Prims.bool) = fun uu____6970 -> get_trace_error ()
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6975 -> get_unthrottle_inductives ()
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6980 -> get_unsafe_tactic_exec ()
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6985 -> get_use_eq_at_higher_order ()
let (use_hints : unit -> Prims.bool) = fun uu____6990 -> get_use_hints ()
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6995 -> get_use_hint_hashes ()
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7002 -> get_use_native_tactics ()
let (use_tactics : unit -> Prims.bool) = fun uu____7007 -> get_use_tactics ()
let (using_facts_from :
  unit ->
    (FStar_Ident.path, Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____7018 ->
    let uu____7019 = get_using_facts_from () in
    match uu____7019 with
    | FStar_Pervasives_Native.None -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7055 ->
    let uu____7056 = get_vcgen_optimize_bind_as_seq () in
    FStar_Option.isSome uu____7056
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7063 ->
    let uu____7064 = get_vcgen_optimize_bind_as_seq () in
    match uu____7064 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7067 -> false
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7074 -> get_warn_default_effects ()
let (z3_exe : unit -> Prims.string) =
  fun uu____7079 ->
    let uu____7080 = get_smt () in
    match uu____7080 with
    | FStar_Pervasives_Native.None -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7090 -> get_z3cliopt ()
let (z3_refresh : unit -> Prims.bool) = fun uu____7095 -> get_z3refresh ()
let (z3_rlimit : unit -> Prims.int) = fun uu____7100 -> get_z3rlimit ()
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7105 -> get_z3rlimit_factor ()
let (z3_seed : unit -> Prims.int) = fun uu____7110 -> get_z3seed ()
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7115 -> get_use_two_phase_tc ()
let (no_positivity : unit -> Prims.bool) =
  fun uu____7120 -> get_no_positivity ()
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7125 -> get_ml_no_eta_expand_coertions ()
let (warn_error : unit -> Prims.string) = fun uu____7130 -> get_warn_error ()
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7135 -> get_use_extracted_interfaces ()
let (should_extract : Prims.string -> Prims.bool) =
  fun m ->
    let m1 = FStar_String.lowercase m in
    let uu____7142 = get_extract () in
    match uu____7142 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7153 =
            let uu____7166 = get_no_extract () in
            let uu____7169 = get_extract_namespace () in
            let uu____7172 = get_extract_module () in
            (uu____7166, uu____7169, uu____7172) in
          match uu____7153 with
          | ([], [], []) -> ()
          | uu____7187 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting in
          let m_components = FStar_Ident.path_of_text m1 in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7233, []) -> true
            | (m2::ms, p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7252 -> false in
          let uu____7261 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7295 ->
                    match uu____7295 with
                    | (path, uu____7303) -> matches_path m_components path)) in
          match uu____7261 with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some (uu____7314, flag) -> flag))
    | FStar_Pervasives_Native.None ->
        let should_extract_namespace m2 =
          let uu____7334 = get_extract_namespace () in
          match uu____7334 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1 ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1))) in
        let should_extract_module m2 =
          let uu____7350 = get_extract_module () in
          match uu____7350 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1 -> (FStar_String.lowercase n1) = m2)) in
        (let uu____7362 = no_extract m1 in Prims.op_Negation uu____7362) &&
          (let uu____7364 =
             let uu____7373 = get_extract_namespace () in
             let uu____7376 = get_extract_module () in
             (uu____7373, uu____7376) in
           (match uu____7364 with
            | ([], []) -> true
            | uu____7387 ->
                (should_extract_namespace m1) || (should_extract_module m1)))