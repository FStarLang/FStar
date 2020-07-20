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
  fun projectee -> match projectee with | Low -> true | uu____14 -> false
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Medium -> true | uu____20 -> false
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | High -> true | uu____26 -> false
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Extreme -> true | uu____32 -> false
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Other _0 -> true | uu____39 -> false
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
  fun projectee -> match projectee with | Bool _0 -> true | uu____79 -> false
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | String _0 -> true | uu____92 -> false
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | Path _0 -> true | uu____105 -> false
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | Path _0 -> _0
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu____118 -> false
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | List _0 -> true | uu____133 -> false
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee -> match projectee with | List _0 -> _0
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Unset -> true | uu____151 -> false
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (__unit_tests : unit -> Prims.bool) =
  fun uu____158 -> FStar_ST.op_Bang __unit_tests__
let (__set_unit_tests : unit -> unit) =
  fun uu____169 -> FStar_ST.op_Colon_Equals __unit_tests__ true
let (__clear_unit_tests : unit -> unit) =
  fun uu____180 -> FStar_ST.op_Colon_Equals __unit_tests__ false
let (as_bool : option_val -> Prims.bool) =
  fun uu___0_191 ->
    match uu___0_191 with
    | Bool b -> b
    | uu____193 -> failwith "Impos: expected Bool"
let (as_int : option_val -> Prims.int) =
  fun uu___1_198 ->
    match uu___1_198 with
    | Int b -> b
    | uu____200 -> failwith "Impos: expected Int"
let (as_string : option_val -> Prims.string) =
  fun uu___2_205 ->
    match uu___2_205 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____208 -> failwith "Impos: expected String"
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___3_215 ->
    match uu___3_215 with
    | List ts -> ts
    | uu____221 -> failwith "Impos: expected List"
let as_list :
  'uuuuuu230 .
    (option_val -> 'uuuuuu230) -> option_val -> 'uuuuuu230 Prims.list
  =
  fun as_t ->
    fun x ->
      let uu____248 = as_list' x in
      FStar_All.pipe_right uu____248 (FStar_List.map as_t)
let as_option :
  'uuuuuu261 .
    (option_val -> 'uuuuuu261) ->
      option_val -> 'uuuuuu261 FStar_Pervasives_Native.option
  =
  fun as_t ->
    fun uu___4_276 ->
      match uu___4_276 with
      | Unset -> FStar_Pervasives_Native.None
      | v -> let uu____280 = as_t v in FStar_Pervasives_Native.Some uu____280
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___5_287 ->
    match uu___5_287 with
    | List ls ->
        let uu____293 =
          FStar_List.map
            (fun l ->
               let uu____303 = as_string l in FStar_Util.split uu____303 ",")
            ls in
        FStar_All.pipe_left FStar_List.flatten uu____293
    | uu____310 -> failwith "Impos: expected String (comma list)"
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'uuuuuu319 . 'uuuuuu319 FStar_Util.smap -> 'uuuuuu319 FStar_Util.smap =
  fun m -> FStar_Util.smap_copy m
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (internal_peek : unit -> optionstate) =
  fun uu____347 ->
    let uu____348 =
      let uu____351 = FStar_ST.op_Bang fstar_options in
      FStar_List.hd uu____351 in
    FStar_List.hd uu____348
let (peek : unit -> optionstate) =
  fun uu____376 ->
    let uu____377 = internal_peek () in copy_optionstate uu____377
let (pop : unit -> unit) =
  fun uu____384 ->
    let uu____385 = FStar_ST.op_Bang fstar_options in
    match uu____385 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____406::[] -> failwith "TOO MANY POPS!"
    | uu____413::tl -> FStar_ST.op_Colon_Equals fstar_options tl
let (push : unit -> unit) =
  fun uu____441 ->
    let uu____442 =
      let uu____447 =
        let uu____450 =
          let uu____453 = FStar_ST.op_Bang fstar_options in
          FStar_List.hd uu____453 in
        FStar_List.map copy_optionstate uu____450 in
      let uu____474 = FStar_ST.op_Bang fstar_options in uu____447 ::
        uu____474 in
    FStar_ST.op_Colon_Equals fstar_options uu____442
let (internal_pop : unit -> Prims.bool) =
  fun uu____513 ->
    let curstack =
      let uu____517 = FStar_ST.op_Bang fstar_options in
      FStar_List.hd uu____517 in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____538::[] -> false
    | uu____539::tl ->
        ((let uu____544 =
            let uu____549 =
              let uu____554 = FStar_ST.op_Bang fstar_options in
              FStar_List.tl uu____554 in
            tl :: uu____549 in
          FStar_ST.op_Colon_Equals fstar_options uu____544);
         true)
let (internal_push : unit -> unit) =
  fun uu____595 ->
    let curstack =
      let uu____599 = FStar_ST.op_Bang fstar_options in
      FStar_List.hd uu____599 in
    let stack' =
      let uu____623 =
        let uu____624 = FStar_List.hd curstack in copy_optionstate uu____624 in
      uu____623 :: curstack in
    let uu____627 =
      let uu____632 =
        let uu____637 = FStar_ST.op_Bang fstar_options in
        FStar_List.tl uu____637 in
      stack' :: uu____632 in
    FStar_ST.op_Colon_Equals fstar_options uu____627
let (set : optionstate -> unit) =
  fun o ->
    let uu____679 = FStar_ST.op_Bang fstar_options in
    match uu____679 with
    | [] -> failwith "set on empty option stack"
    | []::uu____700 -> failwith "set on empty current option stack"
    | (uu____707::tl)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl) :: os)
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____742 -> FStar_Common.snapshot push fstar_options ()
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop fstar_options depth
let (set_option : Prims.string -> option_val -> unit) =
  fun k ->
    fun v ->
      let map = internal_peek () in
      if k = "report_assumes"
      then
        let uu____767 = FStar_Util.smap_try_find map k in
        match uu____767 with
        | FStar_Pervasives_Native.Some (String "error") -> ()
        | uu____770 -> FStar_Util.smap_add map k v
      else FStar_Util.smap_add map k v
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____782 -> match uu____782 with | (k, v) -> set_option k v
let (set_admit_smt_queries : Prims.bool -> unit) =
  fun b -> set_option "admit_smt_queries" (Bool b)
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (add_light_off_file : Prims.string -> unit) =
  fun filename ->
    let uu____805 =
      let uu____808 = FStar_ST.op_Bang light_off_files in filename ::
        uu____808 in
    FStar_ST.op_Colon_Equals light_off_files uu____805
let (defaults : (Prims.string * option_val) Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("abort_on", (Int Prims.int_zero));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("already_cached", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("cache_off", (Bool false));
  ("print_cache_version", (Bool false));
  ("cmi", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("defensive", (String "no"));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("dump_module", (List []));
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
  ("hint_dir", Unset);
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("lsp", (Bool false));
  ("include", (List []));
  ("print", (Bool false));
  ("print_in_place", (Bool false));
  ("force", (Bool false));
  ("fuel", Unset);
  ("ifuel", Unset);
  ("initial_fuel", (Int (Prims.of_int (2))));
  ("initial_ifuel", (Int Prims.int_one));
  ("keep_query_captions", (Bool true));
  ("lax", (Bool false));
  ("load", (List []));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.of_int (8))));
  ("max_ifuel", (Int (Prims.of_int (2))));
  ("min_fuel", (Int Prims.int_one));
  ("MLish", (Bool false));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_load_fstartaclib", (Bool false));
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
  ("print_expected_failures", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("quake", (Int Prims.int_zero));
  ("quake_lo", (Int Prims.int_one));
  ("quake_hi", (Int Prims.int_one));
  ("quake_keep", (Bool false));
  ("query_stats", (Bool false));
  ("record_hints", (Bool false));
  ("record_options", (Bool false));
  ("report_assumes", Unset);
  ("reuse_hint_for", Unset);
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("smtencoding.valid_intro", (Bool true));
  ("smtencoding.valid_elim", (Bool false));
  ("tactics_failhard", (Bool false));
  ("tactics_info", (Bool false));
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int Prims.int_zero));
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
  ("z3rlimit", (Int (Prims.of_int (5))));
  ("z3rlimit_factor", (Int Prims.int_one));
  ("z3seed", (Int Prims.int_zero));
  ("z3cliopt", (List []));
  ("use_two_phase_tc", (Bool true));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("__tactics_nbe", (Bool false));
  ("warn_error", (List []));
  ("use_nbe", (Bool false));
  ("use_nbe_for_extraction", (Bool false));
  ("trivial_pre_for_unannotated_effectful_fns", (Bool true));
  ("profile_group_by_decl", (Bool false));
  ("profile_component", Unset);
  ("profile", Unset)]
let (init : unit -> unit) =
  fun uu____1337 ->
    let o = internal_peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let (clear : unit -> unit) =
  fun uu____1354 ->
    let o = FStar_Util.smap_create (Prims.of_int (50)) in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let (_run : unit) = clear ()
let (get_option : Prims.string -> option_val) =
  fun s ->
    let uu____1393 =
      let uu____1396 = internal_peek () in
      FStar_Util.smap_try_find uu____1396 s in
    match uu____1393 with
    | FStar_Pervasives_Native.None ->
        let uu____1399 =
          let uu____1400 = FStar_String.op_Hat s " not found" in
          FStar_String.op_Hat "Impossible: option " uu____1400 in
        failwith uu____1399
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt :
  'uuuuuu1408 . Prims.string -> (option_val -> 'uuuuuu1408) -> 'uuuuuu1408 =
  fun s -> fun c -> let uu____1424 = get_option s in c uu____1424
let (get_abort_on : unit -> Prims.int) =
  fun uu____1429 -> lookup_opt "abort_on" as_int
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1434 -> lookup_opt "admit_smt_queries" as_bool
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1441 -> lookup_opt "admit_except" (as_option as_string)
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1452 ->
    lookup_opt "already_cached" (as_option (as_list as_string))
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1463 -> lookup_opt "cache_checked_modules" as_bool
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1470 -> lookup_opt "cache_dir" (as_option as_string)
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1477 -> lookup_opt "cache_off" as_bool
let (get_print_cache_version : unit -> Prims.bool) =
  fun uu____1482 -> lookup_opt "print_cache_version" as_bool
let (get_cmi : unit -> Prims.bool) =
  fun uu____1487 -> lookup_opt "cmi" as_bool
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1494 -> lookup_opt "codegen" (as_option as_string)
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1503 -> lookup_opt "codegen-lib" (as_list as_string)
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1512 -> lookup_opt "debug" as_comma_string_list
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1521 -> lookup_opt "debug_level" as_comma_string_list
let (get_defensive : unit -> Prims.string) =
  fun uu____1528 -> lookup_opt "defensive" as_string
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1535 -> lookup_opt "dep" (as_option as_string)
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1542 -> lookup_opt "detail_errors" as_bool
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1547 -> lookup_opt "detail_hint_replay" as_bool
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1554 -> lookup_opt "dump_module" (as_list as_string)
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1561 -> lookup_opt "eager_subtyping" as_bool
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1566 -> lookup_opt "expose_interfaces" as_bool
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1575 -> lookup_opt "extract" (as_option (as_list as_string))
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1588 -> lookup_opt "extract_module" (as_list as_string)
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1597 -> lookup_opt "extract_namespace" (as_list as_string)
let (get_force : unit -> Prims.bool) =
  fun uu____1604 -> lookup_opt "force" as_bool
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1609 -> lookup_opt "fs_typ_app" as_bool
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1614 -> lookup_opt "hide_uvar_nums" as_bool
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1619 -> lookup_opt "hint_info" as_bool
let (get_hint_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1626 -> lookup_opt "hint_dir" (as_option as_string)
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1635 -> lookup_opt "hint_file" (as_option as_string)
let (get_in : unit -> Prims.bool) = fun uu____1642 -> lookup_opt "in" as_bool
let (get_ide : unit -> Prims.bool) =
  fun uu____1647 -> lookup_opt "ide" as_bool
let (get_lsp : unit -> Prims.bool) =
  fun uu____1652 -> lookup_opt "lsp" as_bool
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1659 -> lookup_opt "include" (as_list as_string)
let (get_print : unit -> Prims.bool) =
  fun uu____1666 -> lookup_opt "print" as_bool
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____1671 -> lookup_opt "print_in_place" as_bool
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1676 -> lookup_opt "initial_fuel" as_int
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1681 -> lookup_opt "initial_ifuel" as_int
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____1686 -> lookup_opt "keep_query_captions" as_bool
let (get_lax : unit -> Prims.bool) =
  fun uu____1691 -> lookup_opt "lax" as_bool
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1698 -> lookup_opt "load" (as_list as_string)
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1705 -> lookup_opt "log_queries" as_bool
let (get_log_types : unit -> Prims.bool) =
  fun uu____1710 -> lookup_opt "log_types" as_bool
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1715 -> lookup_opt "max_fuel" as_int
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1720 -> lookup_opt "max_ifuel" as_int
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1725 -> lookup_opt "min_fuel" as_int
let (get_MLish : unit -> Prims.bool) =
  fun uu____1730 -> lookup_opt "MLish" as_bool
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1735 -> lookup_opt "no_default_includes" as_bool
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1742 -> lookup_opt "no_extract" (as_list as_string)
let (get_no_load_fstartaclib : unit -> Prims.bool) =
  fun uu____1749 -> lookup_opt "no_load_fstartaclib" as_bool
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1754 -> lookup_opt "no_location_info" as_bool
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1759 -> lookup_opt "no_plugins" as_bool
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1764 -> lookup_opt "no_smt" as_bool
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1769 -> lookup_opt "normalize_pure_terms_for_extraction" as_bool
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1776 -> lookup_opt "odir" (as_option as_string)
let (get_ugly : unit -> Prims.bool) =
  fun uu____1783 -> lookup_opt "ugly" as_bool
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1790 -> lookup_opt "prims" (as_option as_string)
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1797 -> lookup_opt "print_bound_var_types" as_bool
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1802 -> lookup_opt "print_effect_args" as_bool
let (get_print_expected_failures : unit -> Prims.bool) =
  fun uu____1807 -> lookup_opt "print_expected_failures" as_bool
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1812 -> lookup_opt "print_full_names" as_bool
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1817 -> lookup_opt "print_implicits" as_bool
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1822 -> lookup_opt "print_universes" as_bool
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1827 -> lookup_opt "print_z3_statistics" as_bool
let (get_prn : unit -> Prims.bool) =
  fun uu____1832 -> lookup_opt "prn" as_bool
let (get_quake_lo : unit -> Prims.int) =
  fun uu____1837 -> lookup_opt "quake_lo" as_int
let (get_quake_hi : unit -> Prims.int) =
  fun uu____1842 -> lookup_opt "quake_hi" as_int
let (get_quake_keep : unit -> Prims.bool) =
  fun uu____1847 -> lookup_opt "quake_keep" as_bool
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1852 -> lookup_opt "query_stats" as_bool
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1857 -> lookup_opt "record_hints" as_bool
let (get_record_options : unit -> Prims.bool) =
  fun uu____1862 -> lookup_opt "record_options" as_bool
let (get_retry : unit -> Prims.bool) =
  fun uu____1867 -> lookup_opt "retry" as_bool
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1874 -> lookup_opt "reuse_hint_for" (as_option as_string)
let (get_report_assumes :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1883 -> lookup_opt "report_assumes" (as_option as_string)
let (get_silent : unit -> Prims.bool) =
  fun uu____1890 -> lookup_opt "silent" as_bool
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1897 -> lookup_opt "smt" (as_option as_string)
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1904 -> lookup_opt "smtencoding.elim_box" as_bool
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1909 -> lookup_opt "smtencoding.nl_arith_repr" as_string
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1914 -> lookup_opt "smtencoding.l_arith_repr" as_string
let (get_smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu____1919 -> lookup_opt "smtencoding.valid_intro" as_bool
let (get_smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu____1924 -> lookup_opt "smtencoding.valid_elim" as_bool
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1929 -> lookup_opt "tactic_raw_binders" as_bool
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____1934 -> lookup_opt "tactics_failhard" as_bool
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____1939 -> lookup_opt "tactics_info" as_bool
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1944 -> lookup_opt "tactic_trace" as_bool
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1949 -> lookup_opt "tactic_trace_d" as_int
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1954 -> lookup_opt "__tactics_nbe" as_bool
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____1959 -> lookup_opt "tcnorm" as_bool
let (get_timing : unit -> Prims.bool) =
  fun uu____1964 -> lookup_opt "timing" as_bool
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1969 -> lookup_opt "trace_error" as_bool
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1974 -> lookup_opt "unthrottle_inductives" as_bool
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1979 -> lookup_opt "unsafe_tactic_exec" as_bool
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1984 -> lookup_opt "use_eq_at_higher_order" as_bool
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1989 -> lookup_opt "use_hints" as_bool
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1994 -> lookup_opt "use_hint_hashes" as_bool
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2001 -> lookup_opt "use_native_tactics" (as_option as_string)
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____2008 ->
    let uu____2009 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____2009
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2018 ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2031 ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____2040 -> lookup_opt "verify_module" (as_list as_string)
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____2049 -> lookup_opt "__temp_no_proj" (as_list as_string)
let (get_version : unit -> Prims.bool) =
  fun uu____2056 -> lookup_opt "version" as_bool
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____2061 -> lookup_opt "warn_default_effects" as_bool
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____2068 -> lookup_opt "z3cliopt" (as_list as_string)
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____2075 -> lookup_opt "z3refresh" as_bool
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____2080 -> lookup_opt "z3rlimit" as_int
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____2085 -> lookup_opt "z3rlimit_factor" as_int
let (get_z3seed : unit -> Prims.int) =
  fun uu____2090 -> lookup_opt "z3seed" as_int
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____2095 -> lookup_opt "use_two_phase_tc" as_bool
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____2100 -> lookup_opt "__no_positivity" as_bool
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____2105 -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let (get_warn_error : unit -> Prims.string Prims.list) =
  fun uu____2112 -> lookup_opt "warn_error" (as_list as_string)
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____2119 -> lookup_opt "use_nbe" as_bool
let (get_use_nbe_for_extraction : unit -> Prims.bool) =
  fun uu____2124 -> lookup_opt "use_nbe_for_extraction" as_bool
let (get_trivial_pre_for_unannotated_effectful_fns : unit -> Prims.bool) =
  fun uu____2129 ->
    lookup_opt "trivial_pre_for_unannotated_effectful_fns" as_bool
let (get_profile :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2138 -> lookup_opt "profile" (as_option (as_list as_string))
let (get_profile_group_by_decl : unit -> Prims.bool) =
  fun uu____2149 -> lookup_opt "profile_group_by_decl" as_bool
let (get_profile_component :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2158 ->
    lookup_opt "profile_component" (as_option (as_list as_string))
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___6_2169 ->
    match uu___6_2169 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1 ->
    fun l2 ->
      match l1 with
      | Other uu____2181 -> l1 = l2
      | Low -> l1 = l2
      | Medium -> (l2 = Low) || (l2 = Medium)
      | High -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2 ->
    let uu____2187 = get_debug_level () in
    FStar_All.pipe_right uu____2187
      (FStar_Util.for_some (fun l1 -> one_debug_level_geq (dlevel l1) l2))
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  let sub_dirs = ["legacy"; "experimental"; ".cache"] in
  FStar_All.pipe_right ["/ulib"; "/lib/fstar"]
    (FStar_List.collect
       (fun d ->
          let uu____2206 =
            FStar_All.pipe_right sub_dirs
              (FStar_List.map
                 (fun s ->
                    let uu____2216 = FStar_String.op_Hat "/" s in
                    FStar_String.op_Hat d uu____2216)) in
          d :: uu____2206))
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>"
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (display_version : unit -> unit) =
  fun uu____2231 ->
    let uu____2232 =
      let uu____2233 = FStar_ST.op_Bang _version in
      let uu____2240 = FStar_ST.op_Bang _platform in
      let uu____2247 = FStar_ST.op_Bang _compiler in
      let uu____2254 = FStar_ST.op_Bang _date in
      let uu____2261 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2233
        uu____2240 uu____2247 uu____2254 uu____2261 in
    FStar_Util.print_string uu____2232
let display_usage_aux :
  'uuuuuu2274 'uuuuuu2275 .
    ('uuuuuu2274 * Prims.string * 'uuuuuu2275 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2323 ->
         match uu____2323 with
         | (uu____2334, flag, p, doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2346 =
                      let uu____2347 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2347 in
                    FStar_Util.print_string uu____2346
                  else
                    (let uu____2349 =
                       let uu____2350 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2350 doc in
                     FStar_Util.print_string uu____2349)
              | FStar_Getopt.OneArg (uu____2351, argname) ->
                  if doc = ""
                  then
                    let uu____2359 =
                      let uu____2360 = FStar_Util.colorize_bold flag in
                      let uu____2361 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2360 uu____2361 in
                    FStar_Util.print_string uu____2359
                  else
                    (let uu____2363 =
                       let uu____2364 = FStar_Util.colorize_bold flag in
                       let uu____2365 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2364
                         uu____2365 doc in
                     FStar_Util.print_string uu____2363))) specs
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o ->
    let uu____2391 = o in
    match uu____2391 with
    | (ns, name, arg, desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2424 =
                let uu____2425 = f () in set_option name uu____2425 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f, d) ->
              let g x = let uu____2440 = f x in set_option name uu____2440 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let prev_values =
        let uu____2459 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2459 in
      List (value :: prev_values)
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let prev_values =
        let uu____2485 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2485 in
      List (FStar_List.append prev_values [value])
let accumulate_string :
  'uuuuuu2506 .
    Prims.string -> ('uuuuuu2506 -> Prims.string) -> 'uuuuuu2506 -> unit
  =
  fun name ->
    fun post_processor ->
      fun value ->
        let uu____2527 =
          let uu____2528 =
            let uu____2529 = post_processor value in String uu____2529 in
          accumulated_option name uu____2528 in
        set_option name uu____2527
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
  | OpenEnumStr of (Prims.string Prims.list * Prims.string) 
  | PostProcessed of ((option_val -> option_val) * opt_type) 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of ((unit -> unit) * opt_type) 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____2625 -> false
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | IntStr _0 -> true | uu____2638 -> false
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | IntStr _0 -> _0
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | BoolStr -> true | uu____2650 -> false
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PathStr _0 -> true | uu____2657 -> false
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | PathStr _0 -> _0
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleStr _0 -> true | uu____2670 -> false
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | SimpleStr _0 -> _0
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | EnumStr _0 -> true | uu____2685 -> false
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee -> match projectee with | EnumStr _0 -> _0
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | OpenEnumStr _0 -> true | uu____2710 -> false
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | OpenEnumStr _0 -> _0
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PostProcessed _0 -> true | uu____2748 -> false
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee -> match projectee with | PostProcessed _0 -> _0
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Accumulated _0 -> true | uu____2782 -> false
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | Accumulated _0 -> _0
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2795 -> false
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | ReverseAccumulated _0 -> _0
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | WithSideEffect _0 -> true | uu____2815 -> false
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidArgument uu____2852 -> true
    | uu____2853 -> false
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidArgument uu____2859 -> uu____2859
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name ->
    fun typ ->
      fun str_val ->
        try
          (fun uu___310_2877 ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2879 ->
                      let uu____2880 = FStar_Util.safe_int_of_string str_val in
                      (match uu____2880 with
                       | FStar_Pervasives_Native.Some v -> Int v
                       | FStar_Pervasives_Native.None ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr ->
                      let uu____2884 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name) in
                      Bool uu____2884
                  | PathStr uu____2887 -> Path str_val
                  | SimpleStr uu____2888 -> String str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then String str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2893 -> String str_val
                  | PostProcessed (pp, elem_spec) ->
                      let uu____2908 =
                        parse_opt_val opt_name elem_spec str_val in
                      pp uu____2908
                  | Accumulated elem_spec ->
                      let v = parse_opt_val opt_name elem_spec str_val in
                      accumulated_option opt_name v
                  | ReverseAccumulated elem_spec ->
                      let v = parse_opt_val opt_name elem_spec str_val in
                      reverse_accumulated_option opt_name v
                  | WithSideEffect (side_effect, elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu____2927 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2927
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ ->
    let desc_of_enum cases =
      let uu____2949 =
        let uu____2950 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]" in
        FStar_String.op_Hat "[" uu____2950 in
      FStar_Pervasives_Native.Some uu____2949 in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs, desc) ->
        desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____2966, elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2976, elem_spec) -> desc_of_opt_type elem_spec
let (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name ->
    fun typ ->
      let parser = parse_opt_val opt_name typ in
      let uu____3003 = desc_of_opt_type typ in
      match uu____3003 with
      | FStar_Pervasives_Native.None ->
          FStar_Getopt.ZeroArgs ((fun uu____3009 -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let (pp_validate_dir : option_val -> option_val) =
  fun p -> let pp = as_string p in FStar_Util.mkdir false pp; p
let (pp_lowercase : option_val -> option_val) =
  fun s ->
    let uu____3026 =
      let uu____3027 = as_string s in FStar_String.lowercase uu____3027 in
    String uu____3026
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref Prims.int_zero
let (interp_quake_arg : Prims.string -> (Prims.int * Prims.int * Prims.bool))
  =
  fun s ->
    let ios = FStar_Util.int_of_string in
    match FStar_Util.split s "/" with
    | f::[] ->
        let uu____3061 = ios f in
        let uu____3062 = ios f in (uu____3061, uu____3062, false)
    | f1::f2::[] ->
        if f2 = "k"
        then
          let uu____3071 = ios f1 in
          let uu____3072 = ios f1 in (uu____3071, uu____3072, true)
        else
          (let uu____3074 = ios f1 in
           let uu____3075 = ios f2 in (uu____3074, uu____3075, false))
    | f1::f2::k::[] ->
        if k = "k"
        then
          let uu____3085 = ios f1 in
          let uu____3086 = ios f2 in (uu____3085, uu____3086, true)
        else failwith "unexpected value for --quake"
    | uu____3094 -> failwith "unexpected value for --quake"
let (uu___402 : (((Prims.string -> unit) -> unit) * (Prims.string -> unit)))
  =
  let cb = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set1 f = FStar_ST.op_Colon_Equals cb (FStar_Pervasives_Native.Some f) in
  let call msg =
    let uu____3168 = FStar_ST.op_Bang cb in
    match uu____3168 with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some f -> f msg in
  (set1, call)
let (set_option_warning_callback_aux : (Prims.string -> unit) -> unit) =
  match uu___402 with
  | (set_option_warning_callback_aux, option_warning_callback) ->
      set_option_warning_callback_aux
let (option_warning_callback : Prims.string -> unit) =
  match uu___402 with
  | (set_option_warning_callback_aux1, option_warning_callback) ->
      option_warning_callback
let (set_option_warning_callback : (Prims.string -> unit) -> unit) =
  fun f -> set_option_warning_callback_aux f
let rec (specs_with_types :
  Prims.bool ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun warn_unsafe ->
    [(FStar_Getopt.noshort, "abort_on",
       (PostProcessed
          (((fun uu___7_3324 ->
               match uu___7_3324 with
               | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
               | x -> failwith "?")), (IntStr "non-negative integer"))),
       "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)");
    (FStar_Getopt.noshort, "admit_smt_queries",
      (WithSideEffect
         (((fun uu____3346 ->
              if warn_unsafe
              then option_warning_callback "admit_smt_queries"
              else ())), BoolStr)),
      "Admit SMT queries, unsafe! (default 'false')");
    (FStar_Getopt.noshort, "admit_except",
      (WithSideEffect
         (((fun uu____3360 ->
              if warn_unsafe
              then option_warning_callback "admit_except"
              else ())), (SimpleStr "[symbol|(symbol, id)]"))),
      "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)");
    (FStar_Getopt.noshort, "already_cached",
      (Accumulated
         (SimpleStr
            "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
      "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path");
    (FStar_Getopt.noshort, "cache_checked_modules", (Const (Bool true)),
      "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying");
    (FStar_Getopt.noshort, "cache_dir",
      (PostProcessed (pp_validate_dir, (PathStr "dir"))),
      "Read and write .checked and .checked.lax in directory <dir>");
    (FStar_Getopt.noshort, "cache_off", (Const (Bool true)),
      "Do not read or write any .checked files");
    (FStar_Getopt.noshort, "print_cache_version", (Const (Bool true)),
      "Print the version for .checked files and exit.");
    (FStar_Getopt.noshort, "cmi", (Const (Bool true)),
      "Inline across module interfaces during extraction (aka. cross-module inlining)");
    (FStar_Getopt.noshort, "codegen",
      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
      "Generate code for further compilation to executable code, or build a compiler plugin");
    (FStar_Getopt.noshort, "codegen-lib",
      (Accumulated (SimpleStr "namespace")),
      "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
    (FStar_Getopt.noshort, "debug", (Accumulated (SimpleStr "module_name")),
      "Print lots of debugging information while checking module");
    (FStar_Getopt.noshort, "debug_level",
      (Accumulated
         (OpenEnumStr (["Low"; "Medium"; "High"; "Extreme"], "..."))),
      "Control the verbosity of debugging info");
    (FStar_Getopt.noshort, "defensive",
      (EnumStr ["no"; "warn"; "error"; "abort"]),
      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'error, like 'warn', but the compiler raises a hard error instead \n\t\tif 'abort, like 'warn', but the compiler immediately aborts on an error\n\t\t(default 'no')");
    (FStar_Getopt.noshort, "dep", (EnumStr ["make"; "graph"; "full"; "raw"]),
      "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files");
    (FStar_Getopt.noshort, "detail_errors", (Const (Bool true)),
      "Emit a detailed error report by asking the SMT solver many queries; will take longer");
    (FStar_Getopt.noshort, "detail_hint_replay", (Const (Bool true)),
      "Emit a detailed report for proof whose unsat core fails to replay");
    (FStar_Getopt.noshort, "dump_module",
      (Accumulated (SimpleStr "module_name")), "");
    (FStar_Getopt.noshort, "eager_subtyping", (Const (Bool true)),
      "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)");
    (FStar_Getopt.noshort, "extract",
      (Accumulated
         (SimpleStr
            "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
      "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.");
    (FStar_Getopt.noshort, "extract_module",
      (Accumulated (PostProcessed (pp_lowercase, (SimpleStr "module_name")))),
      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)");
    (FStar_Getopt.noshort, "extract_namespace",
      (Accumulated
         (PostProcessed (pp_lowercase, (SimpleStr "namespace name")))),
      "Deprecated: use --extract instead; Only extract modules in the specified namespace");
    (FStar_Getopt.noshort, "expose_interfaces", (Const (Bool true)),
      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)");
    (FStar_Getopt.noshort, "hide_uvar_nums", (Const (Bool true)),
      "Don't print unification variable numbers");
    (FStar_Getopt.noshort, "hint_dir", (PathStr "path"),
      "Read/write hints to <dir>/module_name.hints (instead of placing hint-file alongside source file)");
    (FStar_Getopt.noshort, "hint_file", (PathStr "path"),
      "Read/write hints to <path> (instead of module-specific hints files; overrides hint_dir)");
    (FStar_Getopt.noshort, "hint_info", (Const (Bool true)),
      "Print information regarding hints (deprecated; use --query_stats instead)");
    (FStar_Getopt.noshort, "in", (Const (Bool true)),
      "Legacy interactive mode; reads input from stdin");
    (FStar_Getopt.noshort, "ide", (Const (Bool true)),
      "JSON-based interactive mode for IDEs");
    (FStar_Getopt.noshort, "lsp", (Const (Bool true)),
      "Language Server Protocol-based interactive mode for IDEs");
    (FStar_Getopt.noshort, "include", (ReverseAccumulated (PathStr "path")),
      "A directory in which to search for files included on the command line");
    (FStar_Getopt.noshort, "print", (Const (Bool true)),
      "Parses and prettyprints the files included on the command line");
    (FStar_Getopt.noshort, "print_in_place", (Const (Bool true)),
      "Parses and prettyprints in place the files included on the command line");
    (102, "force", (Const (Bool true)),
      "Force checking the files given as arguments even if they have valid checked files");
    (FStar_Getopt.noshort, "fuel",
      (PostProcessed
         (((fun uu___8_3640 ->
              match uu___8_3640 with
              | String s ->
                  let p f =
                    let uu____3648 = FStar_Util.int_of_string f in
                    Int uu____3648 in
                  let uu____3649 =
                    match FStar_Util.split s "," with
                    | f::[] -> (f, f)
                    | f1::f2::[] -> (f1, f2)
                    | uu____3661 -> failwith "unexpected value for --fuel" in
                  (match uu____3649 with
                   | (min, max) ->
                       ((let uu____3671 = p min in
                         set_option "initial_fuel" uu____3671);
                        (let uu____3673 = p max in
                         set_option "max_fuel" uu____3673);
                        String s))
              | uu____3674 -> failwith "impos")),
           (SimpleStr "non-negative integer or pair of non-negative integers"))),
      "Set initial_fuel and max_fuel at once");
    (FStar_Getopt.noshort, "ifuel",
      (PostProcessed
         (((fun uu___9_3694 ->
              match uu___9_3694 with
              | String s ->
                  let p f =
                    let uu____3702 = FStar_Util.int_of_string f in
                    Int uu____3702 in
                  let uu____3703 =
                    match FStar_Util.split s "," with
                    | f::[] -> (f, f)
                    | f1::f2::[] -> (f1, f2)
                    | uu____3715 -> failwith "unexpected value for --ifuel" in
                  (match uu____3703 with
                   | (min, max) ->
                       ((let uu____3725 = p min in
                         set_option "initial_ifuel" uu____3725);
                        (let uu____3727 = p max in
                         set_option "max_ifuel" uu____3727);
                        String s))
              | uu____3728 -> failwith "impos")),
           (SimpleStr "non-negative integer or pair of non-negative integers"))),
      "Set initial_ifuel and max_ifuel at once");
    (FStar_Getopt.noshort, "initial_fuel", (IntStr "non-negative integer"),
      "Number of unrolling of recursive functions to try initially (default 2)");
    (FStar_Getopt.noshort, "initial_ifuel", (IntStr "non-negative integer"),
      "Number of unrolling of inductive datatypes to try at first (default 1)");
    (FStar_Getopt.noshort, "keep_query_captions", BoolStr,
      "Retain comments in the logged SMT queries (requires --log_queries; default true)");
    (FStar_Getopt.noshort, "lax",
      (WithSideEffect
         (((fun uu____3765 ->
              if warn_unsafe then option_warning_callback "lax" else ())),
           (Const (Bool true)))),
      "Run the lax-type checker only (admit all verification conditions)");
    (FStar_Getopt.noshort, "load", (ReverseAccumulated (PathStr "module")),
      "Load compiled module");
    (FStar_Getopt.noshort, "log_types", (Const (Bool true)),
      "Print types computed for data/val/let-bindings");
    (FStar_Getopt.noshort, "log_queries", (Const (Bool true)),
      "Log the Z3 queries in several queries-*.smt2 files, as we go");
    (FStar_Getopt.noshort, "max_fuel", (IntStr "non-negative integer"),
      "Number of unrolling of recursive functions to try at most (default 8)");
    (FStar_Getopt.noshort, "max_ifuel", (IntStr "non-negative integer"),
      "Number of unrolling of inductive datatypes to try at most (default 2)");
    (FStar_Getopt.noshort, "min_fuel", (IntStr "non-negative integer"),
      "Minimum number of unrolling of recursive functions to try (default 1)");
    (FStar_Getopt.noshort, "MLish", (Const (Bool true)),
      "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
    (FStar_Getopt.noshort, "no_default_includes", (Const (Bool true)),
      "Ignore the default module search paths");
    (FStar_Getopt.noshort, "no_extract",
      (Accumulated (PathStr "module name")),
      "Deprecated: use --extract instead; Do not extract code from this module");
    (FStar_Getopt.noshort, "no_load_fstartaclib", (Const (Bool true)),
      "Do not attempt to load fstartaclib by default");
    (FStar_Getopt.noshort, "no_location_info", (Const (Bool true)),
      "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
    (FStar_Getopt.noshort, "no_smt", (Const (Bool true)),
      "Do not send any queries to the SMT solver, and fail on them instead");
    (FStar_Getopt.noshort, "normalize_pure_terms_for_extraction",
      (Const (Bool true)),
      "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.");
    (FStar_Getopt.noshort, "odir",
      (PostProcessed (pp_validate_dir, (PathStr "dir"))),
      "Place output in directory <dir>");
    (FStar_Getopt.noshort, "prims", (PathStr "file"), "");
    (FStar_Getopt.noshort, "print_bound_var_types", (Const (Bool true)),
      "Print the types of bound variables");
    (FStar_Getopt.noshort, "print_effect_args", (Const (Bool true)),
      "Print inferred predicate transformers for all computation types");
    (FStar_Getopt.noshort, "print_expected_failures", (Const (Bool true)),
      "Print the errors generated by declarations marked with expect_failure, useful for debugging error locations");
    (FStar_Getopt.noshort, "print_full_names", (Const (Bool true)),
      "Print full names of variables");
    (FStar_Getopt.noshort, "print_implicits", (Const (Bool true)),
      "Print implicit arguments");
    (FStar_Getopt.noshort, "print_universes", (Const (Bool true)),
      "Print universes");
    (FStar_Getopt.noshort, "print_z3_statistics", (Const (Bool true)),
      "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)");
    (FStar_Getopt.noshort, "prn", (Const (Bool true)),
      "Print full names (deprecated; use --print_full_names instead)");
    (FStar_Getopt.noshort, "quake",
      (PostProcessed
         (((fun uu___10_3975 ->
              match uu___10_3975 with
              | String s ->
                  let uu____3977 = interp_quake_arg s in
                  (match uu____3977 with
                   | (min, max, k) ->
                       (set_option "quake_lo" (Int min);
                        set_option "quake_hi" (Int max);
                        set_option "quake_keep" (Bool k);
                        set_option "retry" (Bool false);
                        String s))
              | uu____3991 -> failwith "impos")),
           (SimpleStr "positive integer or pair of positive integers"))),
      "Repeats SMT queries to check for robustness\n\t\t--quake N/M repeats each query checks that it succeeds at least N out of M times, aborting early if possible\n\t\t--quake N/M/k works as above, except it will unconditionally run M times\n\t\t--quake N is an alias for --quake N/N\n\t\t--quake N/k is an alias for --quake N/N/k\n\tUsing --quake disables --retry.");
    (FStar_Getopt.noshort, "query_stats", (Const (Bool true)),
      "Print SMT query statistics");
    (FStar_Getopt.noshort, "record_hints", (Const (Bool true)),
      "Record a database of hints for efficient proof replay");
    (FStar_Getopt.noshort, "record_options", (Const (Bool true)),
      "Record the state of options used to check each sigelt, useful for the `check_with` attribute and metaprogramming");
    (FStar_Getopt.noshort, "retry",
      (PostProcessed
         (((fun uu___11_4033 ->
              match uu___11_4033 with
              | Int i ->
                  (set_option "quake_lo" (Int Prims.int_one);
                   set_option "quake_hi" (Int i);
                   set_option "quake_keep" (Bool false);
                   set_option "retry" (Bool true);
                   Bool true)
              | uu____4039 -> failwith "impos")),
           (IntStr "positive integer"))),
      "Retry each SMT query N times and succeed on the first try. Using --retry disables --quake.");
    (FStar_Getopt.noshort, "reuse_hint_for", (SimpleStr "toplevel_name"),
      "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'");
    (FStar_Getopt.noshort, "report_assumes", (EnumStr ["warn"; "error"]),
      "Report every use of an escape hatch, include assume, admit, etc.");
    (FStar_Getopt.noshort, "silent", (Const (Bool true)),
      "Disable all non-critical output");
    (FStar_Getopt.noshort, "smt", (PathStr "path"),
      "Path to the Z3 SMT solver (we could eventually support other solvers)");
    (FStar_Getopt.noshort, "smtencoding.elim_box", BoolStr,
      "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");
    (FStar_Getopt.noshort, "smtencoding.nl_arith_repr",
      (EnumStr ["native"; "wrapped"; "boxwrap"]),
      "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')");
    (FStar_Getopt.noshort, "smtencoding.l_arith_repr",
      (EnumStr ["native"; "boxwrap"]),
      "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')");
    (FStar_Getopt.noshort, "smtencoding.valid_intro", BoolStr,
      "Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof");
    (FStar_Getopt.noshort, "smtencoding.valid_elim", BoolStr,
      "Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness");
    (FStar_Getopt.noshort, "tactic_raw_binders", (Const (Bool true)),
      "Do not use the lexical scope of tactics to improve binder names");
    (FStar_Getopt.noshort, "tactics_failhard", (Const (Bool true)),
      "Do not recover from metaprogramming errors, and abort if one occurs");
    (FStar_Getopt.noshort, "tactics_info", (Const (Bool true)),
      "Print some rough information on tactics, such as the time they take to run");
    (FStar_Getopt.noshort, "tactic_trace", (Const (Bool true)),
      "Print a depth-indexed trace of tactic execution (Warning: very verbose)");
    (FStar_Getopt.noshort, "tactic_trace_d", (IntStr "positive_integer"),
      "Trace tactics up to a certain binding depth");
    (FStar_Getopt.noshort, "__tactics_nbe", (Const (Bool true)),
      "Use NBE to evaluate metaprograms (experimental)");
    (FStar_Getopt.noshort, "tcnorm", BoolStr,
      "Attempt to normalize definitions marked as tcnorm (default 'true')");
    (FStar_Getopt.noshort, "timing", (Const (Bool true)),
      "Print the time it takes to verify each top-level definition");
    (FStar_Getopt.noshort, "trace_error", (Const (Bool true)),
      "Don't print an error message; show an exception trace instead");
    (FStar_Getopt.noshort, "ugly", (Const (Bool true)),
      "Emit output formatted for debugging");
    (FStar_Getopt.noshort, "unthrottle_inductives", (Const (Bool true)),
      "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
    (FStar_Getopt.noshort, "unsafe_tactic_exec", (Const (Bool true)),
      "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.");
    (FStar_Getopt.noshort, "use_eq_at_higher_order", (Const (Bool true)),
      "Use equality constraints when comparing higher-order types (Temporary)");
    (FStar_Getopt.noshort, "use_hints", (Const (Bool true)),
      "Use a previously recorded hints database for proof replay");
    (FStar_Getopt.noshort, "use_hint_hashes", (Const (Bool true)),
      "Admit queries if their hash matches the hash recorded in the hints database");
    (FStar_Getopt.noshort, "use_native_tactics", (PathStr "path"),
      "Use compiled tactics from <path>");
    (FStar_Getopt.noshort, "no_plugins", (Const (Bool true)),
      "Do not run plugins natively and interpret them as usual instead");
    (FStar_Getopt.noshort, "no_tactics", (Const (Bool true)),
      "Do not run the tactic engine before discharging a VC");
    (FStar_Getopt.noshort, "using_facts_from",
      (ReverseAccumulated
         (SimpleStr
            "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
      "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.");
    (FStar_Getopt.noshort, "vcgen.optimize_bind_as_seq",
      (EnumStr ["off"; "without_type"; "with_type"]),
      "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.");
    (FStar_Getopt.noshort, "__temp_no_proj",
      (Accumulated (SimpleStr "module_name")),
      "Don't generate projectors for this module");
    (FStar_Getopt.noshort, "__temp_fast_implicits", (Const (Bool true)),
      "Don't use this option yet");
    (118, "version",
      (WithSideEffect
         (((fun uu____4301 ->
              display_version (); FStar_All.exit Prims.int_zero)),
           (Const (Bool true)))), "Display version number");
    (FStar_Getopt.noshort, "warn_default_effects", (Const (Bool true)),
      "Warn when (a -> b) is desugared to (a -> Tot b)");
    (FStar_Getopt.noshort, "z3cliopt",
      (ReverseAccumulated (SimpleStr "option")), "Z3 command line options");
    (FStar_Getopt.noshort, "z3refresh", (Const (Bool true)),
      "Restart Z3 after each query; useful for ensuring proof robustness");
    (FStar_Getopt.noshort, "z3rlimit", (IntStr "positive_integer"),
      "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
    (FStar_Getopt.noshort, "z3rlimit_factor", (IntStr "positive_integer"),
      "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");
    (FStar_Getopt.noshort, "z3seed", (IntStr "positive_integer"),
      "Set the Z3 random seed (default 0)");
    (FStar_Getopt.noshort, "use_two_phase_tc", BoolStr,
      "Use the two phase typechecker (default 'true')");
    (FStar_Getopt.noshort, "__no_positivity", (Const (Bool true)),
      "Don't check positivity of inductive types");
    (FStar_Getopt.noshort, "__ml_no_eta_expand_coertions",
      (Const (Bool true)), "Do not eta-expand coertions in generated OCaml");
    (FStar_Getopt.noshort, "warn_error", (Accumulated (SimpleStr "")),
      "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.");
    (FStar_Getopt.noshort, "use_nbe", BoolStr,
      "Use normalization by evaluation as the default normalization strategy (default 'false')");
    (FStar_Getopt.noshort, "use_nbe_for_extraction", BoolStr,
      "Use normalization by evaluation for normalizing terms before extraction (default 'false')");
    (FStar_Getopt.noshort, "trivial_pre_for_unannotated_effectful_fns",
      BoolStr,
      "Enforce trivial preconditions for unannotated effectful functions (default 'true')");
    (FStar_Getopt.noshort, "__debug_embedding",
      (WithSideEffect
         (((fun uu____4419 -> FStar_ST.op_Colon_Equals debug_embedding true)),
           (Const (Bool true)))),
      "Debug messages for embeddings/unembeddings of natively compiled terms");
    (FStar_Getopt.noshort, "eager_embedding",
      (WithSideEffect
         (((fun uu____4438 -> FStar_ST.op_Colon_Equals eager_embedding true)),
           (Const (Bool true)))),
      "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking");
    (FStar_Getopt.noshort, "profile_group_by_decl", (Const (Bool true)),
      "Emit profiles grouped by declaration rather than by module");
    (FStar_Getopt.noshort, "profile_component",
      (Accumulated
         (SimpleStr
            "One or more space-separated occurrences of '[+|-]( * | namespace | module | identifier)'")),
      "\n\tSpecific source locations in the compiler are instrumented with profiling counters.\n\tPass `--profile_component FStar.TypeChecker` to enable all counters in the FStar.TypeChecker namespace.\n\tThis option is a module or namespace selector, like many other options (e.g., `--extract`)");
    (FStar_Getopt.noshort, "profile",
      (Accumulated
         (SimpleStr
            "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
      "\n\tProfiling can be enabled when the compiler is processing a given set of source modules.\n\tPass `--profile FStar.Pervasives` to enable profiling when the compiler is processing any module in FStar.Pervasives.\n\tThis option is a module or namespace selector, like many other options (e.g., `--extract`)");
    (104, "help",
      (WithSideEffect
         (((fun uu____4482 ->
              (let uu____4484 = specs warn_unsafe in
               display_usage_aux uu____4484);
              FStar_All.exit Prims.int_zero)), (Const (Bool true)))),
      "Display this information")]
and (specs : Prims.bool -> FStar_Getopt.opt Prims.list) =
  fun warn_unsafe ->
    let uu____4508 = specs_with_types warn_unsafe in
    FStar_List.map
      (fun uu____4533 ->
         match uu____4533 with
         | (short, long, typ, doc) ->
             let uu____4546 =
               let uu____4557 = arg_spec_of_opt_type long typ in
               (short, long, uu____4557, doc) in
             mk_spec uu____4546) uu____4508
let (settable : Prims.string -> Prims.bool) =
  fun uu___12_4566 ->
    match uu___12_4566 with
    | "abort_on" -> true
    | "admit_except" -> true
    | "admit_smt_queries" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_subtyping" -> true
    | "hide_uvar_nums" -> true
    | "hint_dir" -> true
    | "hint_file" -> true
    | "hint_info" -> true
    | "fuel" -> true
    | "ifuel" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "lax" -> true
    | "load" -> true
    | "log_queries" -> true
    | "log_types" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "no_plugins" -> true
    | "__no_positivity" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "no_smt" -> true
    | "no_tactics" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_expected_failures" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "quake_lo" -> true
    | "quake_hi" -> true
    | "quake_keep" -> true
    | "quake" -> true
    | "query_stats" -> true
    | "record_options" -> true
    | "retry" -> true
    | "reuse_hint_for" -> true
    | "report_assumes" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.l_arith_repr" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "smtencoding.valid_intro" -> true
    | "smtencoding.valid_elim" -> true
    | "tactic_raw_binders" -> true
    | "tactics_failhard" -> true
    | "tactics_info" -> true
    | "__tactics_nbe" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "tcnorm" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "ugly" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "use_two_phase_tc" -> true
    | "using_facts_from" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | "warn_error" -> true
    | "z3cliopt" -> true
    | "z3refresh" -> true
    | "z3rlimit" -> true
    | "z3rlimit_factor" -> true
    | "z3seed" -> true
    | "trivial_pre_for_unannotated_effectful_fns" -> true
    | "profile_group_by_decl" -> true
    | "profile_component" -> true
    | "profile" -> true
    | uu____4567 -> false
let (all_specs : FStar_Getopt.opt Prims.list) = specs true
let (all_specs_with_types :
  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list)
  = specs_with_types true
let (settable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4631 ->
          match uu____4631 with
          | (uu____4642, x, uu____4644, uu____4645) -> settable x))
let (uu___582 :
  (((unit -> FStar_Getopt.parse_cmdline_res) -> unit) *
    (unit -> FStar_Getopt.parse_cmdline_res)))
  =
  let callback = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    FStar_ST.op_Colon_Equals callback (FStar_Pervasives_Native.Some f) in
  let call uu____4714 =
    let uu____4715 = FStar_ST.op_Bang callback in
    match uu____4715 with
    | FStar_Pervasives_Native.None ->
        failwith "Error flags callback not yet set"
    | FStar_Pervasives_Native.Some f -> f () in
  (set1, call)
let (set_error_flags_callback_aux :
  (unit -> FStar_Getopt.parse_cmdline_res) -> unit) =
  match uu___582 with
  | (set_error_flags_callback_aux, set_error_flags) ->
      set_error_flags_callback_aux
let (set_error_flags : unit -> FStar_Getopt.parse_cmdline_res) =
  match uu___582 with
  | (set_error_flags_callback_aux1, set_error_flags) -> set_error_flags
let (set_error_flags_callback :
  (unit -> FStar_Getopt.parse_cmdline_res) -> unit) =
  set_error_flags_callback_aux
let (display_usage : unit -> unit) =
  fun uu____4827 -> display_usage_aux all_specs
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir ()
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____4844 ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i ->
           let uu____4849 =
             let uu____4852 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4852 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4849) in
    let res1 = if res = FStar_Getopt.Success then set_error_flags () else res in
    let uu____4877 =
      let uu____4880 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4880 in
    (res1, uu____4877)
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____4901 -> FStar_ST.op_Bang file_list_
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____4923 = specs false in
       FStar_Getopt.parse_cmdline uu____4923 (fun x -> ()) in
     (let uu____4929 =
        let uu____4934 =
          let uu____4935 =
            FStar_List.map (fun uu____4938 -> String uu____4938)
              old_verify_module in
          List uu____4935 in
        ("verify_module", uu____4934) in
      set_option' uu____4929);
     r)
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____4946 =
        let uu____4947 =
          let uu____4948 =
            let uu____4949 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____4949 in
          (FStar_String.length f1) - uu____4948 in
        uu____4947 - Prims.int_one in
      FStar_String.substring f1 Prims.int_zero uu____4946 in
    FStar_String.lowercase f2
let (should_check : Prims.string -> Prims.bool) =
  fun m ->
    let l = get_verify_module () in
    FStar_List.contains (FStar_String.lowercase m) l
let (should_verify : Prims.string -> Prims.bool) =
  fun m ->
    (let uu____4965 = get_lax () in Prims.op_Negation uu____4965) &&
      (should_check m)
let (should_check_file : Prims.string -> Prims.bool) =
  fun fn ->
    let uu____4971 = module_name_of_file_name fn in should_check uu____4971
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn ->
    let uu____4977 = module_name_of_file_name fn in should_verify uu____4977
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1 ->
    fun m2 -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m ->
    let uu____4993 = get___temp_no_proj () in
    FStar_All.pipe_right uu____4993 (FStar_List.existsb (module_name_eq m))
let (should_print_message : Prims.string -> Prims.bool) =
  fun m ->
    let uu____5003 = should_verify m in
    if uu____5003 then m <> "Prims" else false
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5011 ->
    let cache_dir =
      let uu____5015 = get_cache_dir () in
      match uu____5015 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some c -> [c] in
    let uu____5021 = get_no_default_includes () in
    if uu____5021
    then
      let uu____5024 = get_include () in
      FStar_List.append cache_dir uu____5024
    else
      (let lib_paths =
         let uu____5031 = FStar_Util.expand_environment_variable "FSTAR_LIB" in
         match uu____5031 with
         | FStar_Pervasives_Native.None ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.." in
             let defs = universe_include_path_base_dirs in
             let uu____5040 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x -> FStar_String.op_Hat fstar_home x)) in
             FStar_All.pipe_right uu____5040
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s] in
       let uu____5054 =
         let uu____5057 =
           let uu____5060 = get_include () in
           FStar_List.append uu____5060 ["."] in
         FStar_List.append lib_paths uu____5057 in
       FStar_List.append cache_dir uu____5054)
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.of_int (100)) in
  fun filename ->
    let uu____5077 = FStar_Util.smap_try_find file_map filename in
    match uu____5077 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let result =
          try
            (fun uu___643_5100 ->
               match () with
               | () ->
                   let uu____5103 = FStar_Util.is_path_absolute filename in
                   if uu____5103
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____5110 =
                        let uu____5113 = include_path () in
                        FStar_List.rev uu____5113 in
                      FStar_Util.find_map uu____5110
                        (fun p ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___642_5125 -> FStar_Pervasives_Native.None in
        (if FStar_Option.isSome result
         then FStar_Util.smap_add file_map filename result
         else ();
         result)
let (prims : unit -> Prims.string) =
  fun uu____5136 ->
    let uu____5137 = get_prims () in
    match uu____5137 with
    | FStar_Pervasives_Native.None ->
        let filename = "prims.fst" in
        let uu____5141 = find_file filename in
        (match uu____5141 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None ->
             let uu____5145 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5145)
    | FStar_Pervasives_Native.Some x -> x
let (prims_basename : unit -> Prims.string) =
  fun uu____5151 ->
    let uu____5152 = prims () in FStar_Util.basename uu____5152
let (pervasives : unit -> Prims.string) =
  fun uu____5157 ->
    let filename = "FStar.Pervasives.fsti" in
    let uu____5159 = find_file filename in
    match uu____5159 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None ->
        let uu____5163 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5163
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5168 ->
    let uu____5169 = pervasives () in FStar_Util.basename uu____5169
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5174 ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5176 = find_file filename in
    match uu____5176 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None ->
        let uu____5180 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5180
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname ->
    let uu____5186 = get_odir () in
    match uu____5186 with
    | FStar_Pervasives_Native.None -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath ->
    let uu____5195 = get_cache_dir () in
    match uu____5195 with
    | FStar_Pervasives_Native.None -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5199 = FStar_Util.basename fpath in
        FStar_Util.join_paths x uu____5199
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text -> FStar_String.split [46] text
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns ->
    let cache = FStar_Util.smap_create (Prims.of_int (31)) in
    let with_cache f s =
      let uu____5291 = FStar_Util.smap_try_find cache s in
      match uu____5291 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None ->
          let res = f s in (FStar_Util.smap_add cache s res; res) in
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if s = "-*"
        then ([], false)
        else
          if FStar_Util.starts_with s "-"
          then
            (let path =
               let uu____5400 = FStar_Util.substring_from s Prims.int_one in
               path_of_text uu____5400 in
             (path, false))
          else
            (let s1 =
               if FStar_Util.starts_with s "+"
               then FStar_Util.substring_from s Prims.int_one
               else s in
             ((path_of_text s1), true)) in
    let uu____5408 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s ->
              let s1 = FStar_Util.trim_string s in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2 ->
                     let s3 = FStar_Util.replace_char s2 32 44 in
                     let uu____5460 =
                       let uu____5463 =
                         FStar_All.pipe_right (FStar_Util.splitlines s3)
                           (FStar_List.concatMap
                              (fun s4 -> FStar_Util.split s4 ",")) in
                       FStar_All.pipe_right uu____5463
                         (FStar_List.filter (fun s4 -> s4 <> "")) in
                     FStar_All.pipe_right uu____5460
                       (FStar_List.map parse_one_setting)) s1)) in
    FStar_All.pipe_right uu____5408 FStar_List.rev
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s ->
    let uu____5521 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5521 (FStar_List.contains s)
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____5530 -> lookup_opt "__temp_fast_implicits" as_bool
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____5535 -> get_admit_smt_queries ()
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5542 -> get_admit_except ()
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____5547 -> get_cache_checked_modules ()
let (cache_off : unit -> Prims.bool) = fun uu____5552 -> get_cache_off ()
let (print_cache_version : unit -> Prims.bool) =
  fun uu____5557 -> get_print_cache_version ()
let (cmi : unit -> Prims.bool) = fun uu____5562 -> get_cmi ()
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | OCaml -> true | uu____5568 -> false
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | FSharp -> true | uu____5574 -> false
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Kremlin -> true | uu____5580 -> false
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Plugin -> true | uu____5586 -> false
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____5593 ->
    let uu____5594 = get_codegen () in
    FStar_Util.map_opt uu____5594
      (fun uu___13_5598 ->
         match uu___13_5598 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____5599 -> failwith "Impossible")
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____5608 ->
    let uu____5609 = get_codegen_lib () in
    FStar_All.pipe_right uu____5609
      (FStar_List.map (fun x -> FStar_Util.split x "."))
let (debug_any : unit -> Prims.bool) =
  fun uu____5626 -> let uu____5627 = get_debug () in uu____5627 <> []
let (debug_module : Prims.string -> Prims.bool) =
  fun modul ->
    let uu____5637 = get_debug () in
    FStar_All.pipe_right uu____5637
      (FStar_List.existsb (module_name_eq modul))
let (debug_at_level_no_module : debug_level_t -> Prims.bool) =
  fun level -> debug_level_geq level
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul ->
    fun level -> (debug_module modul) && (debug_at_level_no_module level)
let (profile_group_by_decls : unit -> Prims.bool) =
  fun uu____5661 -> get_profile_group_by_decl ()
let (defensive : unit -> Prims.bool) =
  fun uu____5666 -> let uu____5667 = get_defensive () in uu____5667 <> "no"
let (defensive_error : unit -> Prims.bool) =
  fun uu____5672 -> let uu____5673 = get_defensive () in uu____5673 = "error"
let (defensive_abort : unit -> Prims.bool) =
  fun uu____5678 -> let uu____5679 = get_defensive () in uu____5679 = "abort"
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5686 -> get_dep ()
let (detail_errors : unit -> Prims.bool) =
  fun uu____5691 -> get_detail_errors ()
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____5696 -> get_detail_hint_replay ()
let (dump_module : Prims.string -> Prims.bool) =
  fun s ->
    let uu____5702 = get_dump_module () in
    FStar_All.pipe_right uu____5702 (FStar_List.existsb (module_name_eq s))
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____5711 -> get_eager_subtyping ()
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____5716 -> get_expose_interfaces ()
let (force : unit -> Prims.bool) = fun uu____5721 -> get_force ()
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename ->
    let uu____5727 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5727
let (full_context_dependency : unit -> Prims.bool) = fun uu____5744 -> true
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____5749 -> get_hide_uvar_nums ()
let (hint_info : unit -> Prims.bool) =
  fun uu____5754 -> (get_hint_info ()) || (get_query_stats ())
let (hint_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5761 -> get_hint_dir ()
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5768 -> get_hint_file ()
let (hint_file_for_src : Prims.string -> Prims.string) =
  fun src_filename ->
    let uu____5774 = hint_file () in
    match uu____5774 with
    | FStar_Pervasives_Native.Some fn -> fn
    | FStar_Pervasives_Native.None ->
        let file_name =
          let uu____5779 = hint_dir () in
          match uu____5779 with
          | FStar_Pervasives_Native.Some dir ->
              let uu____5783 = FStar_Util.basename src_filename in
              FStar_Util.concat_dir_filename dir uu____5783
          | uu____5784 -> src_filename in
        FStar_Util.format1 "%s.hints" file_name
let (ide : unit -> Prims.bool) = fun uu____5791 -> get_ide ()
let (print : unit -> Prims.bool) = fun uu____5796 -> get_print ()
let (print_in_place : unit -> Prims.bool) =
  fun uu____5801 -> get_print_in_place ()
let (initial_fuel : unit -> Prims.int) =
  fun uu____5806 ->
    let uu____5807 = get_initial_fuel () in
    let uu____5808 = get_max_fuel () in Prims.min uu____5807 uu____5808
let (initial_ifuel : unit -> Prims.int) =
  fun uu____5813 ->
    let uu____5814 = get_initial_ifuel () in
    let uu____5815 = get_max_ifuel () in Prims.min uu____5814 uu____5815
let (interactive : unit -> Prims.bool) =
  fun uu____5820 -> (get_in ()) || (get_ide ())
let (lax : unit -> Prims.bool) = fun uu____5825 -> get_lax ()
let (load : unit -> Prims.string Prims.list) = fun uu____5832 -> get_load ()
let (legacy_interactive : unit -> Prims.bool) = fun uu____5837 -> get_in ()
let (lsp_server : unit -> Prims.bool) = fun uu____5842 -> get_lsp ()
let (log_queries : unit -> Prims.bool) = fun uu____5847 -> get_log_queries ()
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____5852 -> (log_queries ()) && (get_keep_query_captions ())
let (log_types : unit -> Prims.bool) = fun uu____5857 -> get_log_types ()
let (max_fuel : unit -> Prims.int) = fun uu____5862 -> get_max_fuel ()
let (max_ifuel : unit -> Prims.int) = fun uu____5867 -> get_max_ifuel ()
let (min_fuel : unit -> Prims.int) = fun uu____5872 -> get_min_fuel ()
let (ml_ish : unit -> Prims.bool) = fun uu____5877 -> get_MLish ()
let (set_ml_ish : unit -> unit) =
  fun uu____5882 -> set_option "MLish" (Bool true)
let (no_default_includes : unit -> Prims.bool) =
  fun uu____5887 -> get_no_default_includes ()
let (no_extract : Prims.string -> Prims.bool) =
  fun s ->
    let uu____5893 = get_no_extract () in
    FStar_All.pipe_right uu____5893 (FStar_List.existsb (module_name_eq s))
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____5902 -> get_normalize_pure_terms_for_extraction ()
let (no_load_fstartaclib : unit -> Prims.bool) =
  fun uu____5907 -> get_no_load_fstartaclib ()
let (no_location_info : unit -> Prims.bool) =
  fun uu____5912 -> get_no_location_info ()
let (no_plugins : unit -> Prims.bool) = fun uu____5917 -> get_no_plugins ()
let (no_smt : unit -> Prims.bool) = fun uu____5922 -> get_no_smt ()
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5929 -> get_odir ()
let (ugly : unit -> Prims.bool) = fun uu____5934 -> get_ugly ()
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____5939 -> get_print_bound_var_types ()
let (print_effect_args : unit -> Prims.bool) =
  fun uu____5944 -> get_print_effect_args ()
let (print_expected_failures : unit -> Prims.bool) =
  fun uu____5949 -> get_print_expected_failures ()
let (print_implicits : unit -> Prims.bool) =
  fun uu____5954 -> get_print_implicits ()
let (print_real_names : unit -> Prims.bool) =
  fun uu____5959 -> (get_prn ()) || (get_print_full_names ())
let (print_universes : unit -> Prims.bool) =
  fun uu____5964 -> get_print_universes ()
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____5969 -> get_print_z3_statistics ()
let (quake_lo : unit -> Prims.int) = fun uu____5974 -> get_quake_lo ()
let (quake_hi : unit -> Prims.int) = fun uu____5979 -> get_quake_hi ()
let (quake_keep : unit -> Prims.bool) = fun uu____5984 -> get_quake_keep ()
let (query_stats : unit -> Prims.bool) = fun uu____5989 -> get_query_stats ()
let (record_hints : unit -> Prims.bool) =
  fun uu____5994 -> get_record_hints ()
let (record_options : unit -> Prims.bool) =
  fun uu____5999 -> get_record_options ()
let (retry : unit -> Prims.bool) = fun uu____6004 -> get_retry ()
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6011 -> get_reuse_hint_for ()
let (report_assumes : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6018 -> get_report_assumes ()
let (silent : unit -> Prims.bool) = fun uu____6023 -> get_silent ()
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6028 -> get_smtencoding_elim_box ()
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6033 ->
    let uu____6034 = get_smtencoding_nl_arith_repr () in
    uu____6034 = "native"
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6039 ->
    let uu____6040 = get_smtencoding_nl_arith_repr () in
    uu____6040 = "wrapped"
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6045 ->
    let uu____6046 = get_smtencoding_nl_arith_repr () in
    uu____6046 = "boxwrap"
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6051 ->
    let uu____6052 = get_smtencoding_l_arith_repr () in uu____6052 = "native"
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6057 ->
    let uu____6058 = get_smtencoding_l_arith_repr () in
    uu____6058 = "boxwrap"
let (smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu____6063 -> get_smtencoding_valid_intro ()
let (smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu____6068 -> get_smtencoding_valid_elim ()
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6073 -> get_tactic_raw_binders ()
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____6078 -> get_tactics_failhard ()
let (tactics_info : unit -> Prims.bool) =
  fun uu____6083 -> get_tactics_info ()
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6088 -> get_tactic_trace ()
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6093 -> get_tactic_trace_d ()
let (tactics_nbe : unit -> Prims.bool) = fun uu____6098 -> get_tactics_nbe ()
let (tcnorm : unit -> Prims.bool) = fun uu____6103 -> get_tcnorm ()
let (timing : unit -> Prims.bool) = fun uu____6108 -> get_timing ()
let (trace_error : unit -> Prims.bool) = fun uu____6113 -> get_trace_error ()
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6118 -> get_unthrottle_inductives ()
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6123 -> get_unsafe_tactic_exec ()
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6128 -> get_use_eq_at_higher_order ()
let (use_hints : unit -> Prims.bool) = fun uu____6133 -> get_use_hints ()
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6138 -> get_use_hint_hashes ()
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6145 -> get_use_native_tactics ()
let (use_tactics : unit -> Prims.bool) = fun uu____6150 -> get_use_tactics ()
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____6163 ->
    let uu____6164 = get_using_facts_from () in
    match uu____6164 with
    | FStar_Pervasives_Native.None -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6202 ->
    let uu____6203 = get_vcgen_optimize_bind_as_seq () in
    FStar_Option.isSome uu____6203
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6210 ->
    let uu____6211 = get_vcgen_optimize_bind_as_seq () in
    match uu____6211 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6214 -> false
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6221 -> get_warn_default_effects ()
let (warn_error : unit -> Prims.string) =
  fun uu____6226 ->
    let uu____6227 = get_warn_error () in FStar_String.concat " " uu____6227
let (z3_exe : unit -> Prims.string) =
  fun uu____6234 ->
    let uu____6235 = get_smt () in
    match uu____6235 with
    | FStar_Pervasives_Native.None -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6245 -> get_z3cliopt ()
let (z3_refresh : unit -> Prims.bool) = fun uu____6250 -> get_z3refresh ()
let (z3_rlimit : unit -> Prims.int) = fun uu____6255 -> get_z3rlimit ()
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6260 -> get_z3rlimit_factor ()
let (z3_seed : unit -> Prims.int) = fun uu____6265 -> get_z3seed ()
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6270 ->
    (get_use_two_phase_tc ()) &&
      (let uu____6272 = lax () in Prims.op_Negation uu____6272)
let (no_positivity : unit -> Prims.bool) =
  fun uu____6277 -> get_no_positivity ()
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6282 -> get_ml_no_eta_expand_coertions ()
let (use_nbe : unit -> Prims.bool) = fun uu____6287 -> get_use_nbe ()
let (use_nbe_for_extraction : unit -> Prims.bool) =
  fun uu____6292 -> get_use_nbe_for_extraction ()
let (trivial_pre_for_unannotated_effectful_fns : unit -> Prims.bool) =
  fun uu____6297 -> get_trivial_pre_for_unannotated_effectful_fns ()
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let uu____6313 =
      let uu____6314 = trace_error () in Prims.op_Negation uu____6314 in
    if uu____6313
    then
      (push ();
       (let r =
          try
            (fun uu___857_6327 ->
               match () with
               | () -> let uu____6332 = f () in FStar_Util.Inr uu____6332) ()
          with | uu___856_6334 -> FStar_Util.Inl uu___856_6334 in
        pop ();
        (match r with
         | FStar_Util.Inr v -> v
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f () in pop (); retv))
let (module_matches_namespace_filter :
  Prims.string -> Prims.string Prims.list -> Prims.bool) =
  fun m ->
    fun filter ->
      let m1 = FStar_String.lowercase m in
      let setting = parse_settings filter in
      let m_components = path_of_text m1 in
      let rec matches_path m_components1 path =
        match (m_components1, path) with
        | (uu____6396, []) -> true
        | (m2::ms, p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____6415 -> false in
      let uu____6424 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____6458 ->
                match uu____6458 with
                | (path, uu____6466) -> matches_path m_components path)) in
      match uu____6424 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____6477, flag) -> flag
let (matches_namespace_filter_opt :
  Prims.string ->
    Prims.string Prims.list FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun m ->
    fun uu___14_6502 ->
      match uu___14_6502 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some filter ->
          module_matches_namespace_filter m filter
let (should_extract : Prims.string -> Prims.bool) =
  fun m ->
    let m1 = FStar_String.lowercase m in
    let uu____6520 = get_extract () in
    match uu____6520 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____6531 =
            let uu____6544 = get_no_extract () in
            let uu____6547 = get_extract_namespace () in
            let uu____6550 = get_extract_module () in
            (uu____6544, uu____6547, uu____6550) in
          match uu____6531 with
          | ([], [], []) -> ()
          | uu____6565 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None ->
        let should_extract_namespace m2 =
          let uu____6586 = get_extract_namespace () in
          match uu____6586 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n))) in
        let should_extract_module m2 =
          let uu____6602 = get_extract_module () in
          match uu____6602 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n -> (FStar_String.lowercase n) = m2)) in
        (let uu____6614 = no_extract m1 in Prims.op_Negation uu____6614) &&
          (let uu____6616 =
             let uu____6625 = get_extract_namespace () in
             let uu____6628 = get_extract_module () in
             (uu____6625, uu____6628) in
           (match uu____6616 with
            | ([], []) -> true
            | uu____6639 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6653 = get_already_cached () in
    match uu____6653 with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
let (profile_enabled :
  Prims.string FStar_Pervasives_Native.option -> Prims.string -> Prims.bool)
  =
  fun modul_opt ->
    fun phase ->
      match modul_opt with
      | FStar_Pervasives_Native.None ->
          let uu____6679 = get_profile_component () in
          matches_namespace_filter_opt phase uu____6679
      | FStar_Pervasives_Native.Some modul ->
          (let uu____6687 = get_profile () in
           matches_namespace_filter_opt modul uu____6687) &&
            (let uu____6693 = get_profile_component () in
             matches_namespace_filter_opt phase uu____6693)
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | File_argument uu____6707 -> true
    | uu____6708 -> false
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | File_argument uu____6714 -> uu____6714
let (set_options : Prims.string -> FStar_Getopt.parse_cmdline_res) =
  fun s ->
    try
      (fun uu___942_6721 ->
         match () with
         | () ->
             if s = ""
             then FStar_Getopt.Success
             else
               (let res =
                  FStar_Getopt.parse_string settable_specs
                    (fun s1 -> FStar_Exn.raise (File_argument s1)) s in
                if res = FStar_Getopt.Success
                then set_error_flags ()
                else res)) ()
    with
    | File_argument s1 ->
        let uu____6734 =
          FStar_Util.format1 "File %s is not a valid option" s1 in
        FStar_Getopt.Error uu____6734