open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____11 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____17 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____23 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____29 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____36 -> false
  
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
    match projectee with | Bool _0 -> true | uu____77 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____91 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____105 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____119 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____135 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____154 -> false
  
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
  fun projectee  -> match projectee with | Set  -> true | uu____182 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____188 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____194 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____212  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____236  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____260  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___75_284  ->
    match uu___75_284 with
    | Bool b -> b
    | uu____286 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___76_291  ->
    match uu___76_291 with
    | Int b -> b
    | uu____293 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___77_298  ->
    match uu___77_298 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____301 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___78_308  ->
    match uu___78_308 with
    | List ts -> ts
    | uu____314 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____323 .
    (option_val -> 'Auu____323) -> option_val -> 'Auu____323 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____341 = as_list' x  in
      FStar_All.pipe_right uu____341 (FStar_List.map as_t)
  
let as_option :
  'Auu____354 .
    (option_val -> 'Auu____354) ->
      option_val -> 'Auu____354 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___79_369  ->
      match uu___79_369 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____373 = as_t v1  in FStar_Pervasives_Native.Some uu____373
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___80_380  ->
    match uu___80_380 with
    | List ls ->
        let uu____386 =
          FStar_List.map
            (fun l  ->
               let uu____396 = as_string l  in FStar_Util.split uu____396 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____386
    | uu____403 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____429  ->
    let uu____430 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____430
  
let (pop : unit -> unit) =
  fun uu____460  ->
    let uu____461 = FStar_ST.op_Bang fstar_options  in
    match uu____461 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____487::[] -> failwith "TOO MANY POPS!"
    | uu____488::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____519  ->
    let uu____520 =
      let uu____523 =
        let uu____524 = peek ()  in FStar_Util.smap_copy uu____524  in
      let uu____527 = FStar_ST.op_Bang fstar_options  in uu____523 ::
        uu____527
       in
    FStar_ST.op_Colon_Equals fstar_options uu____520
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____581 = FStar_ST.op_Bang fstar_options  in
    match uu____581 with
    | [] -> failwith "set on empty option stack"
    | uu____607::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____642  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____662 = peek ()  in FStar_Util.smap_add uu____662 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____673  -> match uu____673 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____720 =
      let uu____723 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____723
       in
    FStar_ST.op_Colon_Equals light_off_files uu____720
  
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
  fun uu____1178  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1195  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1252 =
      let uu____1255 = peek ()  in FStar_Util.smap_try_find uu____1255 s  in
    match uu____1252 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1265 . Prims.string -> (option_val -> 'Auu____1265) -> 'Auu____1265
  = fun s  -> fun c  -> let uu____1281 = get_option s  in c uu____1281 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1286  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1291  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1298  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1305  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1312  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1319  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1326  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1335  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1344  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1353  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1360  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1367  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1374  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1379  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1384  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1391  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1398  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1403  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1412  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1425  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1434  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1441  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1446  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1451  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1458  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1465  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1470  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1477  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1484  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1489  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1494  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1499  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1506  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1513  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1518  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1523  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1528  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1533  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1538  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1543  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1548  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1555  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1562  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1567  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1572  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1579  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1586  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1593  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1600  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1605  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1610  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1615  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1620  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1625  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1630  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1635  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1640  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1647  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1654  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1661  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1668  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1673  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1678  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1683  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1688  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1693  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1698  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____1703  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1708  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1713  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1718  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1723  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1728  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1733  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1738  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1745  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1752  ->
    let uu____1753 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1753
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1762  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1775  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1784  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1793  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1800  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1805  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1812  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1819  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1824  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1829  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1834  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1839  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1844  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1849  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1854  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1859  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1864  ->
    match uu___81_1864 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1876 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1882 = get_debug_level ()  in
    FStar_All.pipe_right uu____1882
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2015  ->
    let uu____2016 =
      let uu____2017 = FStar_ST.op_Bang _version  in
      let uu____2037 = FStar_ST.op_Bang _platform  in
      let uu____2057 = FStar_ST.op_Bang _compiler  in
      let uu____2077 = FStar_ST.op_Bang _date  in
      let uu____2097 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2017
        uu____2037 uu____2057 uu____2077 uu____2097
       in
    FStar_Util.print_string uu____2016
  
let display_usage_aux :
  'Auu____2123 'Auu____2124 .
    ('Auu____2123,Prims.string,'Auu____2124 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2172  ->
         match uu____2172 with
         | (uu____2183,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2195 =
                      let uu____2196 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2196  in
                    FStar_Util.print_string uu____2195
                  else
                    (let uu____2198 =
                       let uu____2199 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2199 doc  in
                     FStar_Util.print_string uu____2198)
              | FStar_Getopt.OneArg (uu____2200,argname) ->
                  if doc = ""
                  then
                    let uu____2208 =
                      let uu____2209 = FStar_Util.colorize_bold flag  in
                      let uu____2210 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2209 uu____2210
                       in
                    FStar_Util.print_string uu____2208
                  else
                    (let uu____2212 =
                       let uu____2213 = FStar_Util.colorize_bold flag  in
                       let uu____2214 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2213
                         uu____2214 doc
                        in
                     FStar_Util.print_string uu____2212))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2242 = o  in
    match uu____2242 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2278 =
                let uu____2279 = f ()  in set_option name uu____2279  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2294 = f x  in set_option name uu____2294
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2314 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2314  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2337 =
        let uu____2340 = lookup_opt name as_list'  in
        FStar_List.append uu____2340 [value]  in
      mk_list uu____2337
  
let accumulate_string :
  'Auu____2353 .
    Prims.string -> ('Auu____2353 -> Prims.string) -> 'Auu____2353 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2374 =
          let uu____2375 =
            let uu____2376 = post_processor value  in mk_string uu____2376
             in
          accumulated_option name uu____2375  in
        set_option name uu____2374
  
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
    match projectee with | Const _0 -> true | uu____2472 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2486 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2499 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2506 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2520 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2536 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2562 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2601 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2636 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2650 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2671 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2709 -> true
    | uu____2710 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2717 -> uu____2717
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___86_2735  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2737 ->
                      let uu____2738 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2738 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2742 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2742
                  | PathStr uu____2745 -> mk_path str_val
                  | SimpleStr uu____2746 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2751 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2766 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2766
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
            let uu____2785 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2785
  
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
    | PostProcessed (uu____2822,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2832,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2859 = desc_of_opt_type typ  in
      match uu____2859 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2865  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2882 =
      let uu____2883 = as_string s  in FStar_String.lowercase uu____2883  in
    mk_string uu____2882
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2931  ->
    let uu____2943 =
      let uu____2955 =
        let uu____2967 =
          let uu____2979 =
            let uu____2989 =
              let uu____2990 = mk_bool true  in Const uu____2990  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____2989,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____2992 =
            let uu____3004 =
              let uu____3016 =
                let uu____3026 =
                  let uu____3027 = mk_bool true  in Const uu____3027  in
                (FStar_Getopt.noshort, "cache_off", uu____3026,
                  "Do not read or write any .checked files")
                 in
              let uu____3029 =
                let uu____3041 =
                  let uu____3053 =
                    let uu____3065 =
                      let uu____3077 =
                        let uu____3089 =
                          let uu____3101 =
                            let uu____3113 =
                              let uu____3123 =
                                let uu____3124 = mk_bool true  in
                                Const uu____3124  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3123,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3126 =
                              let uu____3138 =
                                let uu____3148 =
                                  let uu____3149 = mk_bool true  in
                                  Const uu____3149  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3148,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3151 =
                                let uu____3163 =
                                  let uu____3173 =
                                    let uu____3174 = mk_bool true  in
                                    Const uu____3174  in
                                  (FStar_Getopt.noshort, "doc", uu____3173,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3176 =
                                  let uu____3188 =
                                    let uu____3200 =
                                      let uu____3210 =
                                        let uu____3211 = mk_bool true  in
                                        Const uu____3211  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3210,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3213 =
                                      let uu____3225 =
                                        let uu____3235 =
                                          let uu____3236 = mk_bool true  in
                                          Const uu____3236  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3235,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3238 =
                                        let uu____3250 =
                                          let uu____3262 =
                                            let uu____3274 =
                                              let uu____3286 =
                                                let uu____3296 =
                                                  let uu____3297 =
                                                    mk_bool true  in
                                                  Const uu____3297  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3296,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3299 =
                                                let uu____3311 =
                                                  let uu____3321 =
                                                    let uu____3322 =
                                                      mk_bool true  in
                                                    Const uu____3322  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3321,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3324 =
                                                  let uu____3336 =
                                                    let uu____3348 =
                                                      let uu____3358 =
                                                        let uu____3359 =
                                                          mk_bool true  in
                                                        Const uu____3359  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3358,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3361 =
                                                      let uu____3373 =
                                                        let uu____3383 =
                                                          let uu____3384 =
                                                            mk_bool true  in
                                                          Const uu____3384
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3383,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3386 =
                                                        let uu____3398 =
                                                          let uu____3408 =
                                                            let uu____3409 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3409
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3408,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3411 =
                                                          let uu____3423 =
                                                            let uu____3435 =
                                                              let uu____3445
                                                                =
                                                                let uu____3446
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3446
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3445,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3448 =
                                                              let uu____3460
                                                                =
                                                                let uu____3472
                                                                  =
                                                                  let uu____3484
                                                                    =
                                                                    let uu____3494
                                                                    =
                                                                    let uu____3495
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3495
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3494,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3497
                                                                    =
                                                                    let uu____3509
                                                                    =
                                                                    let uu____3521
                                                                    =
                                                                    let uu____3531
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3532
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3531,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3557
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3556,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3559
                                                                    =
                                                                    let uu____3571
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3595
                                                                    =
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3618
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3618
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3617,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3632
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3654
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3655
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3654,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3657
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3681
                                                                    =
                                                                    let uu____3691
                                                                    =
                                                                    let uu____3692
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3692
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3691,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3694
                                                                    =
                                                                    let uu____3706
                                                                    =
                                                                    let uu____3716
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3717
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3716,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3731
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3742
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3742
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3741,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3756
                                                                    =
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3780
                                                                    =
                                                                    let uu____3790
                                                                    =
                                                                    let uu____3791
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3791
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3790,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3793
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3815
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3816
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3815,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3840,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3843
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    let uu____3866
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3866
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3865,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3868
                                                                    =
                                                                    let uu____3880
                                                                    =
                                                                    let uu____3890
                                                                    =
                                                                    let uu____3891
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3891
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3890,
                                                                    "Print universes")
                                                                     in
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
                                                                    "print_z3_statistics",
                                                                    uu____3915,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3918
                                                                    =
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3941
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3940,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3943
                                                                    =
                                                                    let uu____3955
                                                                    =
                                                                    let uu____3965
                                                                    =
                                                                    let uu____3966
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3966
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3965,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3968
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    let uu____3990
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3991
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3990,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3993
                                                                    =
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4027
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4028
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4027,
                                                                    " ")  in
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4042
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    let uu____4066
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4101
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4100,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4103
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4125
                                                                    =
                                                                    let uu____4126
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4126
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4125,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4128
                                                                    =
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
                                                                    "__tactics_nbe",
                                                                    uu____4162,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4199
                                                                    =
                                                                    let uu____4200
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4200
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4199,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4202
                                                                    =
                                                                    let uu____4214
                                                                    =
                                                                    let uu____4224
                                                                    =
                                                                    let uu____4225
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4225
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4224,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4227
                                                                    =
                                                                    let uu____4239
                                                                    =
                                                                    let uu____4249
                                                                    =
                                                                    let uu____4250
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4250
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4249,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4252
                                                                    =
                                                                    let uu____4264
                                                                    =
                                                                    let uu____4274
                                                                    =
                                                                    let uu____4275
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4275
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4274,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4277
                                                                    =
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4299
                                                                    =
                                                                    let uu____4300
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4300
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4299,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4302
                                                                    =
                                                                    let uu____4314
                                                                    =
                                                                    let uu____4324
                                                                    =
                                                                    let uu____4325
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4325
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4324,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4327
                                                                    =
                                                                    let uu____4339
                                                                    =
                                                                    let uu____4349
                                                                    =
                                                                    let uu____4350
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4350
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4349,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4352
                                                                    =
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4374
                                                                    =
                                                                    let uu____4375
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4375
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4374,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4377
                                                                    =
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
                                                                    "no_tactics",
                                                                    uu____4411,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4414
                                                                    =
                                                                    let uu____4426
                                                                    =
                                                                    let uu____4438
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    let uu____4462
                                                                    =
                                                                    let uu____4472
                                                                    =
                                                                    let uu____4473
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4473
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4472,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4497
                                                                    =
                                                                    let uu____4498
                                                                    =
                                                                    let uu____4506
                                                                    =
                                                                    let uu____4507
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4507
                                                                     in
                                                                    ((fun
                                                                    uu____4513
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4506)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4498
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4497,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4517
                                                                    =
                                                                    let uu____4529
                                                                    =
                                                                    let uu____4539
                                                                    =
                                                                    let uu____4540
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4540
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4539,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4542
                                                                    =
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4566
                                                                    =
                                                                    let uu____4576
                                                                    =
                                                                    let uu____4577
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4577
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4576,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4579
                                                                    =
                                                                    let uu____4591
                                                                    =
                                                                    let uu____4603
                                                                    =
                                                                    let uu____4615
                                                                    =
                                                                    let uu____4627
                                                                    =
                                                                    let uu____4639
                                                                    =
                                                                    let uu____4649
                                                                    =
                                                                    let uu____4650
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4650
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4649,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4652
                                                                    =
                                                                    let uu____4664
                                                                    =
                                                                    let uu____4674
                                                                    =
                                                                    let uu____4675
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4674,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4677
                                                                    =
                                                                    let uu____4689
                                                                    =
                                                                    let uu____4701
                                                                    =
                                                                    let uu____4713
                                                                    =
                                                                    let uu____4723
                                                                    =
                                                                    let uu____4724
                                                                    =
                                                                    let uu____4732
                                                                    =
                                                                    let uu____4733
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4733
                                                                     in
                                                                    ((fun
                                                                    uu____4739
                                                                     ->
                                                                    (
                                                                    let uu____4741
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4741);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4732)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4724
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4723,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4713]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4701
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4689
                                                                     in
                                                                    uu____4664
                                                                    ::
                                                                    uu____4677
                                                                     in
                                                                    uu____4639
                                                                    ::
                                                                    uu____4652
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4627
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4603
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4591
                                                                     in
                                                                    uu____4566
                                                                    ::
                                                                    uu____4579
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4554
                                                                     in
                                                                    uu____4529
                                                                    ::
                                                                    uu____4542
                                                                     in
                                                                    uu____4487
                                                                    ::
                                                                    uu____4517
                                                                     in
                                                                    uu____4462
                                                                    ::
                                                                    uu____4475
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4450
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4438
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4426
                                                                     in
                                                                    uu____4401
                                                                    ::
                                                                    uu____4414
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4389
                                                                     in
                                                                    uu____4364
                                                                    ::
                                                                    uu____4377
                                                                     in
                                                                    uu____4339
                                                                    ::
                                                                    uu____4352
                                                                     in
                                                                    uu____4314
                                                                    ::
                                                                    uu____4327
                                                                     in
                                                                    uu____4289
                                                                    ::
                                                                    uu____4302
                                                                     in
                                                                    uu____4264
                                                                    ::
                                                                    uu____4277
                                                                     in
                                                                    uu____4239
                                                                    ::
                                                                    uu____4252
                                                                     in
                                                                    uu____4214
                                                                    ::
                                                                    uu____4227
                                                                     in
                                                                    uu____4189
                                                                    ::
                                                                    uu____4202
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4177
                                                                     in
                                                                    uu____4152
                                                                    ::
                                                                    uu____4165
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4140
                                                                     in
                                                                    uu____4115
                                                                    ::
                                                                    uu____4128
                                                                     in
                                                                    uu____4090
                                                                    ::
                                                                    uu____4103
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4054
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4042
                                                                     in
                                                                    uu____4017
                                                                    ::
                                                                    uu____4030
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4005
                                                                     in
                                                                    uu____3980
                                                                    ::
                                                                    uu____3993
                                                                     in
                                                                    uu____3955
                                                                    ::
                                                                    uu____3968
                                                                     in
                                                                    uu____3930
                                                                    ::
                                                                    uu____3943
                                                                     in
                                                                    uu____3905
                                                                    ::
                                                                    uu____3918
                                                                     in
                                                                    uu____3880
                                                                    ::
                                                                    uu____3893
                                                                     in
                                                                    uu____3855
                                                                    ::
                                                                    uu____3868
                                                                     in
                                                                    uu____3830
                                                                    ::
                                                                    uu____3843
                                                                     in
                                                                    uu____3805
                                                                    ::
                                                                    uu____3818
                                                                     in
                                                                    uu____3780
                                                                    ::
                                                                    uu____3793
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3756
                                                                     in
                                                                    uu____3731
                                                                    ::
                                                                    uu____3744
                                                                     in
                                                                    uu____3706
                                                                    ::
                                                                    uu____3719
                                                                     in
                                                                    uu____3681
                                                                    ::
                                                                    uu____3694
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3669
                                                                     in
                                                                    uu____3644
                                                                    ::
                                                                    uu____3657
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3632
                                                                     in
                                                                    uu____3607
                                                                    ::
                                                                    uu____3620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3583
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3571
                                                                     in
                                                                    uu____3546
                                                                    ::
                                                                    uu____3559
                                                                     in
                                                                    uu____3521
                                                                    ::
                                                                    uu____3534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3509
                                                                     in
                                                                  uu____3484
                                                                    ::
                                                                    uu____3497
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3472
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3460
                                                               in
                                                            uu____3435 ::
                                                              uu____3448
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3423
                                                           in
                                                        uu____3398 ::
                                                          uu____3411
                                                         in
                                                      uu____3373 ::
                                                        uu____3386
                                                       in
                                                    uu____3348 :: uu____3361
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3336
                                                   in
                                                uu____3311 :: uu____3324  in
                                              uu____3286 :: uu____3299  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3274
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3262
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3250
                                         in
                                      uu____3225 :: uu____3238  in
                                    uu____3200 :: uu____3213  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3188
                                   in
                                uu____3163 :: uu____3176  in
                              uu____3138 :: uu____3151  in
                            uu____3113 :: uu____3126  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3101
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3089
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3077
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3065
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3053
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3041
                 in
              uu____3016 :: uu____3029  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3004
             in
          uu____2979 :: uu____2992  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____2967
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____2955
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5677  ->
             match uu___82_5677 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____2943

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5700  ->
    let uu____5703 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5730  ->
         match uu____5730 with
         | (short,long,typ,doc) ->
             let uu____5746 =
               let uu____5758 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5758, doc)  in
             mk_spec uu____5746) uu____5703

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5768  ->
    match uu___83_5768 with
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
    | "no_tactics" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "tactic_raw_binders" -> true
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
    | uu____5769 -> false
  
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
       (fun uu____5843  ->
          match uu____5843 with
          | (uu____5855,x,uu____5857,uu____5858) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5920  ->
          match uu____5920 with
          | (uu____5932,x,uu____5934,uu____5935) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5946  ->
    let uu____5947 = specs ()  in display_usage_aux uu____5947
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5971 -> true
    | uu____5972 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5979 -> uu____5979
  
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
        (fun uu___88_5996  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6007 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6007
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6035  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6040 =
             let uu____6043 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6043 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6040)
       in
    let uu____6092 =
      let uu____6095 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6095
       in
    (res, uu____6092)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6129  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6164 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6164 (fun x  -> ())  in
     (let uu____6170 =
        let uu____6175 =
          let uu____6176 = FStar_List.map mk_string old_verify_module  in
          List uu____6176  in
        ("verify_module", uu____6175)  in
      set_option' uu____6170);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6186 =
        let uu____6187 =
          let uu____6188 =
            let uu____6189 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6189  in
          (FStar_String.length f1) - uu____6188  in
        uu____6187 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6186  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6195 = get_lax ()  in
    if uu____6195
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6205 = module_name_of_file_name fn  in should_verify uu____6205
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6211 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6211
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6219 = should_verify m  in
    if uu____6219 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6227  ->
    let uu____6228 = get_no_default_includes ()  in
    if uu____6228
    then get_include ()
    else
      (let lib_paths =
         let uu____6235 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6235 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6244 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6244
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6258 =
         let uu____6261 = get_include ()  in
         FStar_List.append uu____6261 ["."]  in
       FStar_List.append lib_paths uu____6258)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6274 = FStar_Util.smap_try_find file_map filename  in
    match uu____6274 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___90_6287  ->
               match () with
               | () ->
                   let uu____6290 = FStar_Util.is_path_absolute filename  in
                   if uu____6290
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6297 =
                        let uu____6300 = include_path ()  in
                        FStar_List.rev uu____6300  in
                      FStar_Util.find_map uu____6297
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___89_6312 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6323  ->
    let uu____6324 = get_prims ()  in
    match uu____6324 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6328 = find_file filename  in
        (match uu____6328 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6332 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6332)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6338  ->
    let uu____6339 = prims ()  in FStar_Util.basename uu____6339
  
let (pervasives : unit -> Prims.string) =
  fun uu____6344  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6346 = find_file filename  in
    match uu____6346 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6350 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6350
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6355  ->
    let uu____6356 = pervasives ()  in FStar_Util.basename uu____6356
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6361  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6363 = find_file filename  in
    match uu____6363 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6367 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6367
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6373 = get_odir ()  in
    match uu____6373 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6382 = get_cache_dir ()  in
    match uu____6382 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6386 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6386
  
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
             let uu____6452 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6452  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6460 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6460 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6530 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6530 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6539  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6544  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6551  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6556  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6561  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6567 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6573 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6579 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6585 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6592  ->
    let uu____6593 = get_codegen ()  in
    FStar_Util.map_opt uu____6593
      (fun uu___84_6597  ->
         match uu___84_6597 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6598 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6607  ->
    let uu____6608 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6608
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6625  -> let uu____6626 = get_debug ()  in uu____6626 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6636 = get_debug ()  in
    FStar_All.pipe_right uu____6636 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6653 = get_debug ()  in
       FStar_All.pipe_right uu____6653 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6662  -> let uu____6663 = get_defensive ()  in uu____6663 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6668  ->
    let uu____6669 = get_defensive ()  in uu____6669 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6676  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6681  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6686  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6691  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6697 = get_dump_module ()  in
    FStar_All.pipe_right uu____6697 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6706  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6711  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6717 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6717
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6747  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6752  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6757  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6764  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6769  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6774  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6779  ->
    let uu____6780 = get_initial_fuel ()  in
    let uu____6781 = get_max_fuel ()  in Prims.min uu____6780 uu____6781
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6786  ->
    let uu____6787 = get_initial_ifuel ()  in
    let uu____6788 = get_max_ifuel ()  in Prims.min uu____6787 uu____6788
  
let (interactive : unit -> Prims.bool) =
  fun uu____6793  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6798  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6805  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6810  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6815  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6820  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6825  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6830  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6835  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6840  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6845  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6850  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6855  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6862 = get_no_extract ()  in
    FStar_All.pipe_right uu____6862
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6873  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6878  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6883  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6890  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6895  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6900  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6905  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6910  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6915  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6920  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6925  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6930  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6935  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6942  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6947  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6952  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6957  ->
    let uu____6958 = get_smtencoding_nl_arith_repr ()  in
    uu____6958 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6963  ->
    let uu____6964 = get_smtencoding_nl_arith_repr ()  in
    uu____6964 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6969  ->
    let uu____6970 = get_smtencoding_nl_arith_repr ()  in
    uu____6970 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6975  ->
    let uu____6976 = get_smtencoding_l_arith_repr ()  in
    uu____6976 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6981  ->
    let uu____6982 = get_smtencoding_l_arith_repr ()  in
    uu____6982 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6987  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6992  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6997  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7002  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7007  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7012  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7017  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7022  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7027  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7032  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7037  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7042  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7049  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7054  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7067  ->
    let uu____7068 = get_using_facts_from ()  in
    match uu____7068 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7106  ->
    let uu____7107 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7107
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7114  ->
    let uu____7115 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7115 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7118 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7125  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7130  ->
    let uu____7131 = get_smt ()  in
    match uu____7131 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7141  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7146  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7151  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7156  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7161  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7166  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7168 = lax ()  in Prims.op_Negation uu____7168)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7173  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7178  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7183  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7188  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7195 = get_extract ()  in
    match uu____7195 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7206 =
            let uu____7219 = get_no_extract ()  in
            let uu____7222 = get_extract_namespace ()  in
            let uu____7225 = get_extract_module ()  in
            (uu____7219, uu____7222, uu____7225)  in
          match uu____7206 with
          | ([],[],[]) -> ()
          | uu____7240 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7288,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7307 -> false  in
          let uu____7316 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7350  ->
                    match uu____7350 with
                    | (path,uu____7358) -> matches_path m_components path))
             in
          match uu____7316 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7369,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7389 = get_extract_namespace ()  in
          match uu____7389 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7405 = get_extract_module ()  in
          match uu____7405 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7417 = no_extract m1  in Prims.op_Negation uu____7417) &&
          (let uu____7419 =
             let uu____7428 = get_extract_namespace ()  in
             let uu____7431 = get_extract_module ()  in
             (uu____7428, uu____7431)  in
           (match uu____7419 with
            | ([],[]) -> true
            | uu____7442 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  