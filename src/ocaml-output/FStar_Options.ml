open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string [@@deriving show]
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
  | Unset [@@deriving show]
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
  | Restore [@@deriving show]
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
  fun uu____240  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____268  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___38_296  ->
    match uu___38_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___39_303  ->
    match uu___39_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___40_310  ->
    match uu___40_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___41_320  ->
    match uu___41_320 with
    | List ts -> ts
    | uu____326 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____335 .
    (option_val -> 'Auu____335) -> option_val -> 'Auu____335 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____353 = as_list' x  in
      FStar_All.pipe_right uu____353 (FStar_List.map as_t)
  
let as_option :
  'Auu____366 .
    (option_val -> 'Auu____366) ->
      option_val -> 'Auu____366 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___42_381  ->
      match uu___42_381 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____385 = as_t v1  in FStar_Pervasives_Native.Some uu____385
  
type optionstate = option_val FStar_Util.smap[@@deriving show]
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____409  ->
    let uu____410 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____410
  
let (pop : unit -> unit) =
  fun uu____444  ->
    let uu____445 = FStar_ST.op_Bang fstar_options  in
    match uu____445 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____475::[] -> failwith "TOO MANY POPS!"
    | uu____476::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____511  ->
    let uu____512 =
      let uu____515 =
        let uu____518 = peek ()  in FStar_Util.smap_copy uu____518  in
      let uu____521 = FStar_ST.op_Bang fstar_options  in uu____515 ::
        uu____521
       in
    FStar_ST.op_Colon_Equals fstar_options uu____512
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____587 = FStar_ST.op_Bang fstar_options  in
    match uu____587 with
    | [] -> failwith "set on empty option stack"
    | uu____617::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____658 = peek ()  in FStar_Util.smap_add uu____658 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____669  -> match uu____669 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____716 =
      let uu____719 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____719
       in
    FStar_ST.op_Colon_Equals light_off_files uu____716
  
let (defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
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
  fun uu____1166  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1183  ->
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
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1286  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1293  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1300  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1307  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1316  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1325  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1334  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1343  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1350  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1357  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1364  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1369  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1374  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1381  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : unit -> Prims.bool) =
  fun uu____1388  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1393  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1402  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1415  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1424  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1431  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1438  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1445  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1450  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1457  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1464  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1469  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1476  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1483  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1488  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1493  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1498  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1505  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1512  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1517  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1522  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1527  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1532  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1537  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1542  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1547  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1554  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1561  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1566  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1571  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1578  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1585  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1592  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1599  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1604  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1609  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1614  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1619  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1624  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1629  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1634  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1639  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1646  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1653  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1660  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1667  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1672  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1677  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1682  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1687  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1692  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1697  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1702  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1707  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1712  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1717  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1722  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1727  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1734  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1741  ->
    let uu____1742 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1742
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1751  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1764  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1773  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1782  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1789  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1794  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1801  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1808  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1813  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1818  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1823  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1828  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1833  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1838  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1843  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1848  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___43_1853  ->
    match uu___43_1853 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1865 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1871 = get_debug_level ()  in
    FStar_All.pipe_right uu____1871
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2004  ->
    let uu____2005 =
      let uu____2006 = FStar_ST.op_Bang _version  in
      let uu____2030 = FStar_ST.op_Bang _platform  in
      let uu____2054 = FStar_ST.op_Bang _compiler  in
      let uu____2078 = FStar_ST.op_Bang _date  in
      let uu____2102 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2006
        uu____2030 uu____2054 uu____2078 uu____2102
       in
    FStar_Util.print_string uu____2005
  
let display_usage_aux :
  'Auu____2132 'Auu____2133 .
    ('Auu____2132,Prims.string,'Auu____2133 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2181  ->
         match uu____2181 with
         | (uu____2192,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2204 =
                      let uu____2205 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2205  in
                    FStar_Util.print_string uu____2204
                  else
                    (let uu____2207 =
                       let uu____2208 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2208 doc  in
                     FStar_Util.print_string uu____2207)
              | FStar_Getopt.OneArg (uu____2209,argname) ->
                  if doc = ""
                  then
                    let uu____2217 =
                      let uu____2218 = FStar_Util.colorize_bold flag  in
                      let uu____2219 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2218 uu____2219
                       in
                    FStar_Util.print_string uu____2217
                  else
                    (let uu____2221 =
                       let uu____2222 = FStar_Util.colorize_bold flag  in
                       let uu____2223 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2222
                         uu____2223 doc
                        in
                     FStar_Util.print_string uu____2221))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2249 = o  in
    match uu____2249 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2282 =
                let uu____2283 = f ()  in set_option name uu____2283  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2298 = f x  in set_option name uu____2298
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2317 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2317  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2340 =
        let uu____2343 = lookup_opt name as_list'  in
        FStar_List.append uu____2343 [value]  in
      mk_list uu____2340
  
let accumulate_string :
  'Auu____2356 .
    Prims.string -> ('Auu____2356 -> Prims.string) -> 'Auu____2356 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2377 =
          let uu____2378 =
            let uu____2379 = post_processor value  in mk_string uu____2379
             in
          accumulated_option name uu____2378  in
        set_option name uu____2377
  
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
[@@deriving show]
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2475 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2489 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2502 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2509 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2523 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2539 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2565 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2604 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2639 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2653 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2674 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2712 -> true
    | uu____2713 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2720 -> uu____2720
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2740 ->
              let uu____2741 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2741 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2745 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2745
          | PathStr uu____2748 -> mk_path str_val
          | SimpleStr uu____2749 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2754 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2769 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2769
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val  in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val  in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect,elem_spec) ->
              (side_effect (); parse_opt_val opt_name elem_spec str_val)
        with
        | InvalidArgument opt_name1 ->
            let uu____2788 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2788
  
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
    | PostProcessed (uu____2825,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2835,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2862 = desc_of_opt_type typ  in
      match uu____2862 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2868  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2885 =
      let uu____2886 = as_string s  in FStar_String.lowercase uu____2886  in
    mk_string uu____2885
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2907  ->
    let uu____2918 =
      let uu____2929 =
        let uu____2940 =
          let uu____2949 = let uu____2950 = mk_bool true  in Const uu____2950
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2949,
            "Write a '.checked' file for each module after verification")
           in
        let uu____2951 =
          let uu____2962 =
            let uu____2973 =
              let uu____2984 =
                let uu____2995 =
                  let uu____3006 =
                    let uu____3017 =
                      let uu____3028 =
                        let uu____3039 =
                          let uu____3048 =
                            let uu____3049 = mk_bool true  in
                            Const uu____3049  in
                          (FStar_Getopt.noshort, "detail_errors", uu____3048,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____3050 =
                          let uu____3061 =
                            let uu____3070 =
                              let uu____3071 = mk_bool true  in
                              Const uu____3071  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3070,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____3072 =
                            let uu____3083 =
                              let uu____3092 =
                                let uu____3093 = mk_bool true  in
                                Const uu____3093  in
                              (FStar_Getopt.noshort, "doc", uu____3092,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____3094 =
                              let uu____3105 =
                                let uu____3116 =
                                  let uu____3125 =
                                    let uu____3126 = mk_bool true  in
                                    Const uu____3126  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____3125,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____3127 =
                                  let uu____3138 =
                                    let uu____3149 =
                                      let uu____3160 =
                                        let uu____3171 =
                                          let uu____3180 =
                                            let uu____3181 = mk_bool true  in
                                            Const uu____3181  in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____3180,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                           in
                                        let uu____3182 =
                                          let uu____3193 =
                                            let uu____3204 =
                                              let uu____3213 =
                                                let uu____3214 = mk_bool true
                                                   in
                                                Const uu____3214  in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____3213,
                                                "Don't print unification variable numbers")
                                               in
                                            let uu____3215 =
                                              let uu____3226 =
                                                let uu____3237 =
                                                  let uu____3246 =
                                                    let uu____3247 =
                                                      mk_bool true  in
                                                    Const uu____3247  in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____3246,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)")
                                                   in
                                                let uu____3248 =
                                                  let uu____3259 =
                                                    let uu____3268 =
                                                      let uu____3269 =
                                                        mk_bool true  in
                                                      Const uu____3269  in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____3268,
                                                      "Legacy interactive mode; reads input from stdin")
                                                     in
                                                  let uu____3270 =
                                                    let uu____3281 =
                                                      let uu____3290 =
                                                        let uu____3291 =
                                                          mk_bool true  in
                                                        Const uu____3291  in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____3290,
                                                        "JSON-based interactive mode for IDEs")
                                                       in
                                                    let uu____3292 =
                                                      let uu____3303 =
                                                        let uu____3314 =
                                                          let uu____3323 =
                                                            let uu____3324 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3324
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____3323,
                                                            "Parses and outputs the files on the command line")
                                                           in
                                                        let uu____3325 =
                                                          let uu____3336 =
                                                            let uu____3347 =
                                                              let uu____3358
                                                                =
                                                                let uu____3367
                                                                  =
                                                                  let uu____3368
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____3368
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____3367,
                                                                  "Run the lax-type checker only (admit all verification conditions)")
                                                                 in
                                                              let uu____3369
                                                                =
                                                                let uu____3380
                                                                  =
                                                                  let uu____3391
                                                                    =
                                                                    let uu____3400
                                                                    =
                                                                    let uu____3401
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3401
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3400,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                  let uu____3402
                                                                    =
                                                                    let uu____3413
                                                                    =
                                                                    let uu____3422
                                                                    =
                                                                    let uu____3423
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3423
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3422,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3424
                                                                    =
                                                                    let uu____3435
                                                                    =
                                                                    let uu____3446
                                                                    =
                                                                    let uu____3457
                                                                    =
                                                                    let uu____3468
                                                                    =
                                                                    let uu____3477
                                                                    =
                                                                    let uu____3478
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3478
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3477,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3479
                                                                    =
                                                                    let uu____3490
                                                                    =
                                                                    let uu____3501
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3511
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3510,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3512
                                                                    =
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3543
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3544
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3543,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3545
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3565
                                                                    =
                                                                    let uu____3566
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3566
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3565,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3567
                                                                    =
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3587
                                                                    =
                                                                    let uu____3588
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3588
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3587,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3622
                                                                    =
                                                                    let uu____3631
                                                                    =
                                                                    let uu____3632
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3632
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3631,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3653
                                                                    =
                                                                    let uu____3654
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3654
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3653,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3655
                                                                    =
                                                                    let uu____3666
                                                                    =
                                                                    let uu____3675
                                                                    =
                                                                    let uu____3676
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3676
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3675,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3677
                                                                    =
                                                                    let uu____3688
                                                                    =
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3698
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3698
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3697,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3699
                                                                    =
                                                                    let uu____3710
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3720
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3720
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3719,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3721
                                                                    =
                                                                    let uu____3732
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
                                                                    "print_z3_statistics",
                                                                    uu____3741,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3743
                                                                    =
                                                                    let uu____3754
                                                                    =
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3764
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3764
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3763,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3765
                                                                    =
                                                                    let uu____3776
                                                                    =
                                                                    let uu____3785
                                                                    =
                                                                    let uu____3786
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3786
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3785,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3787
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3807
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3808
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3807,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3809
                                                                    =
                                                                    let uu____3820
                                                                    =
                                                                    let uu____3831
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
                                                                    "silent",
                                                                    uu____3840,
                                                                    " ")  in
                                                                    let uu____3842
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    let uu____3875
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    let uu____3897
                                                                    =
                                                                    let uu____3906
                                                                    =
                                                                    let uu____3907
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3907
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3906,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3908
                                                                    =
                                                                    let uu____3919
                                                                    =
                                                                    let uu____3928
                                                                    =
                                                                    let uu____3929
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3929
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3928,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    let uu____3952
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3962
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3961,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3974
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3984
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3983,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3985
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4006
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4006
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4005,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4007
                                                                    =
                                                                    let uu____4018
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
                                                                    "unthrottle_inductives",
                                                                    uu____4027,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4029
                                                                    =
                                                                    let uu____4040
                                                                    =
                                                                    let uu____4049
                                                                    =
                                                                    let uu____4050
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4050
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4049,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4051
                                                                    =
                                                                    let uu____4062
                                                                    =
                                                                    let uu____4071
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4072
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4071,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4073
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    let uu____4093
                                                                    =
                                                                    let uu____4094
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4094
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4093,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4095
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4116
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4115,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4117
                                                                    =
                                                                    let uu____4128
                                                                    =
                                                                    let uu____4139
                                                                    =
                                                                    let uu____4148
                                                                    =
                                                                    let uu____4149
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4149
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4148,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4150
                                                                    =
                                                                    let uu____4161
                                                                    =
                                                                    let uu____4172
                                                                    =
                                                                    let uu____4183
                                                                    =
                                                                    let uu____4194
                                                                    =
                                                                    let uu____4203
                                                                    =
                                                                    let uu____4204
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4204
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4203,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4205
                                                                    =
                                                                    let uu____4216
                                                                    =
                                                                    let uu____4226
                                                                    =
                                                                    let uu____4227
                                                                    =
                                                                    let uu____4235
                                                                    =
                                                                    let uu____4236
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4236
                                                                     in
                                                                    ((fun
                                                                    uu____4242
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4235)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4227
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4226,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4246
                                                                    =
                                                                    let uu____4258
                                                                    =
                                                                    let uu____4267
                                                                    =
                                                                    let uu____4268
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4268
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4267,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4269
                                                                    =
                                                                    let uu____4280
                                                                    =
                                                                    let uu____4291
                                                                    =
                                                                    let uu____4300
                                                                    =
                                                                    let uu____4301
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4301
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4300,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4302
                                                                    =
                                                                    let uu____4313
                                                                    =
                                                                    let uu____4324
                                                                    =
                                                                    let uu____4335
                                                                    =
                                                                    let uu____4346
                                                                    =
                                                                    let uu____4357
                                                                    =
                                                                    let uu____4366
                                                                    =
                                                                    let uu____4367
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4367
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4366,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4368
                                                                    =
                                                                    let uu____4379
                                                                    =
                                                                    let uu____4388
                                                                    =
                                                                    let uu____4389
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4389
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4388,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4390
                                                                    =
                                                                    let uu____4401
                                                                    =
                                                                    let uu____4412
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4422
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____4421,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____4423
                                                                    =
                                                                    let uu____4434
                                                                    =
                                                                    let uu____4444
                                                                    =
                                                                    let uu____4445
                                                                    =
                                                                    let uu____4453
                                                                    =
                                                                    let uu____4454
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4454
                                                                     in
                                                                    ((fun
                                                                    uu____4460
                                                                     ->
                                                                    (
                                                                    let uu____4462
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4462);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4453)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4445
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4444,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4434]
                                                                     in
                                                                    uu____4412
                                                                    ::
                                                                    uu____4423
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4401
                                                                     in
                                                                    uu____4379
                                                                    ::
                                                                    uu____4390
                                                                     in
                                                                    uu____4357
                                                                    ::
                                                                    uu____4368
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4346
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4335
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4324
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4313
                                                                     in
                                                                    uu____4291
                                                                    ::
                                                                    uu____4302
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4280
                                                                     in
                                                                    uu____4258
                                                                    ::
                                                                    uu____4269
                                                                     in
                                                                    uu____4216
                                                                    ::
                                                                    uu____4246
                                                                     in
                                                                    uu____4194
                                                                    ::
                                                                    uu____4205
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4183
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4172
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4161
                                                                     in
                                                                    uu____4139
                                                                    ::
                                                                    uu____4150
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4128
                                                                     in
                                                                    uu____4106
                                                                    ::
                                                                    uu____4117
                                                                     in
                                                                    uu____4084
                                                                    ::
                                                                    uu____4095
                                                                     in
                                                                    uu____4062
                                                                    ::
                                                                    uu____4073
                                                                     in
                                                                    uu____4040
                                                                    ::
                                                                    uu____4051
                                                                     in
                                                                    uu____4018
                                                                    ::
                                                                    uu____4029
                                                                     in
                                                                    uu____3996
                                                                    ::
                                                                    uu____4007
                                                                     in
                                                                    uu____3974
                                                                    ::
                                                                    uu____3985
                                                                     in
                                                                    uu____3952
                                                                    ::
                                                                    uu____3963
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3941
                                                                     in
                                                                    uu____3919
                                                                    ::
                                                                    uu____3930
                                                                     in
                                                                    uu____3897
                                                                    ::
                                                                    uu____3908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3886
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3875
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3864
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3853
                                                                     in
                                                                    uu____3831
                                                                    ::
                                                                    uu____3842
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3820
                                                                     in
                                                                    uu____3798
                                                                    ::
                                                                    uu____3809
                                                                     in
                                                                    uu____3776
                                                                    ::
                                                                    uu____3787
                                                                     in
                                                                    uu____3754
                                                                    ::
                                                                    uu____3765
                                                                     in
                                                                    uu____3732
                                                                    ::
                                                                    uu____3743
                                                                     in
                                                                    uu____3710
                                                                    ::
                                                                    uu____3721
                                                                     in
                                                                    uu____3688
                                                                    ::
                                                                    uu____3699
                                                                     in
                                                                    uu____3666
                                                                    ::
                                                                    uu____3677
                                                                     in
                                                                    uu____3644
                                                                    ::
                                                                    uu____3655
                                                                     in
                                                                    uu____3622
                                                                    ::
                                                                    uu____3633
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3611
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3600
                                                                     in
                                                                    uu____3578
                                                                    ::
                                                                    uu____3589
                                                                     in
                                                                    uu____3556
                                                                    ::
                                                                    uu____3567
                                                                     in
                                                                    uu____3534
                                                                    ::
                                                                    uu____3545
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3523
                                                                     in
                                                                    uu____3501
                                                                    ::
                                                                    uu____3512
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3490
                                                                     in
                                                                    uu____3468
                                                                    ::
                                                                    uu____3479
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3457
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3446
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3435
                                                                     in
                                                                    uu____3413
                                                                    ::
                                                                    uu____3424
                                                                     in
                                                                  uu____3391
                                                                    ::
                                                                    uu____3402
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____3380
                                                                 in
                                                              uu____3358 ::
                                                                uu____3369
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____3347
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____3336
                                                           in
                                                        uu____3314 ::
                                                          uu____3325
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____3303
                                                       in
                                                    uu____3281 :: uu____3292
                                                     in
                                                  uu____3259 :: uu____3270
                                                   in
                                                uu____3237 :: uu____3248  in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____3226
                                               in
                                            uu____3204 :: uu____3215  in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____3193
                                           in
                                        uu____3171 :: uu____3182  in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____3160
                                       in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____3149
                                     in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____3138
                                   in
                                uu____3116 :: uu____3127  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____3105
                               in
                            uu____3083 :: uu____3094  in
                          uu____3061 :: uu____3072  in
                        uu____3039 :: uu____3050  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3028
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____3017
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____3006
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2995
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2984
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2973
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2962
           in
        uu____2940 :: uu____2951  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2929
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2918

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5222  ->
    let uu____5225 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5250  ->
         match uu____5250 with
         | (short,long,typ,doc) ->
             let uu____5263 =
               let uu____5274 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5274, doc)  in
             mk_spec uu____5263) uu____5225

let (settable : Prims.string -> Prims.bool) =
  fun uu___44_5283  ->
    match uu___44_5283 with
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
    | uu____5284 -> false
  
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
       (fun uu____5343  ->
          match uu____5343 with
          | (uu____5354,x,uu____5356,uu____5357) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5403  ->
          match uu____5403 with
          | (uu____5414,x,uu____5416,uu____5417) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5426  ->
    let uu____5427 = specs ()  in display_usage_aux uu____5427
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5444  ->
    let uu____5445 = get_fstar_home ()  in
    match uu____5445 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5451 =
            let uu____5456 = mk_string x1  in ("fstar_home", uu____5456)  in
          set_option' uu____5451);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5467 -> true
    | uu____5468 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5475 -> uu____5475
  
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
        if s = ""
        then FStar_Getopt.Success
        else
          FStar_Getopt.parse_string specs1
            (fun s1  -> FStar_Exn.raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____5523 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5523
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5551  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5556 =
             let uu____5559 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5559 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5556)
       in
    let uu____5616 =
      let uu____5619 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5619
       in
    (res, uu____5616)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5657  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5696 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5696 (fun x  -> ())  in
     (let uu____5702 =
        let uu____5707 =
          let uu____5708 = FStar_List.map mk_string old_verify_module  in
          List uu____5708  in
        ("verify_module", uu____5707)  in
      set_option' uu____5702);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5718 =
        let uu____5719 =
          let uu____5720 =
            let uu____5721 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5721  in
          (FStar_String.length f1) - uu____5720  in
        uu____5719 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5718  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5727 = get_lax ()  in
    if uu____5727
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5737 = module_name_of_file_name fn  in should_verify uu____5737
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5743 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5743
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5751 = should_verify m  in
    if uu____5751 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5759  ->
    let uu____5760 = get_no_default_includes ()  in
    if uu____5760
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5768 =
         let uu____5771 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5771
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5784 =
         let uu____5787 = get_include ()  in
         FStar_List.append uu____5787 ["."]  in
       FStar_List.append uu____5768 uu____5784)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5797 = FStar_Util.is_path_absolute filename  in
    if uu____5797
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5804 =
         let uu____5807 = include_path ()  in FStar_List.rev uu____5807  in
       FStar_Util.find_map uu____5804
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____5822  ->
    let uu____5823 = get_prims ()  in
    match uu____5823 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5827 = find_file filename  in
        (match uu____5827 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5831 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5831)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____5837  ->
    let uu____5838 = prims ()  in FStar_Util.basename uu____5838
  
let (pervasives : unit -> Prims.string) =
  fun uu____5843  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5845 = find_file filename  in
    match uu____5845 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5849 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5849
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5854  ->
    let uu____5855 = pervasives ()  in FStar_Util.basename uu____5855
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5860  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5862 = find_file filename  in
    match uu____5862 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5866 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5866
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5872 = get_odir ()  in
    match uu____5872 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5881 = get_cache_dir ()  in
    match uu____5881 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5885 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5885
  
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
             let uu____5939 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5939  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5943 = FStar_Ident.path_of_text s1  in
           (uu____5943, true))
       in
    let uu____5944 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5944 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6014 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6014 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6023  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6028  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6035  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6040  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6046 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6052 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6058 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6064 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6071  ->
    let uu____6072 = get_codegen ()  in
    FStar_Util.map_opt uu____6072
      (fun uu___45_6076  ->
         match uu___45_6076 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6077 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6086  ->
    let uu____6087 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6087
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6104  -> let uu____6105 = get_debug ()  in uu____6105 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6115 = get_debug ()  in
    FStar_All.pipe_right uu____6115 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6132 = get_debug ()  in
       FStar_All.pipe_right uu____6132 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6141  -> let uu____6142 = get_defensive ()  in uu____6142 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6147  ->
    let uu____6148 = get_defensive ()  in uu____6148 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6155  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6160  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6165  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6170  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6176 = get_dump_module ()  in
    FStar_All.pipe_right uu____6176 (FStar_List.contains s)
  
let (eager_inference : unit -> Prims.bool) =
  fun uu____6185  -> get_eager_inference () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6190  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6196 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6196
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6230  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6235  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6240  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6247  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6252  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6257  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6262  ->
    let uu____6263 = get_initial_fuel ()  in
    let uu____6264 = get_max_fuel ()  in Prims.min uu____6263 uu____6264
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6269  ->
    let uu____6270 = get_initial_ifuel ()  in
    let uu____6271 = get_max_ifuel ()  in Prims.min uu____6270 uu____6271
  
let (interactive : unit -> Prims.bool) =
  fun uu____6276  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6281  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6288  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6293  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6298  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6303  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6308  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6313  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6318  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6323  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6328  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6333  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6338  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6345 = get_no_extract ()  in
    FStar_All.pipe_right uu____6345
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6356  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6361  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6366  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6373  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6378  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6383  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6388  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6393  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6398  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6403  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6408  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6413  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6418  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6425  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6430  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6435  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6440  ->
    let uu____6441 = get_smtencoding_nl_arith_repr ()  in
    uu____6441 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6446  ->
    let uu____6447 = get_smtencoding_nl_arith_repr ()  in
    uu____6447 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6452  ->
    let uu____6453 = get_smtencoding_nl_arith_repr ()  in
    uu____6453 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6458  ->
    let uu____6459 = get_smtencoding_l_arith_repr ()  in
    uu____6459 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6464  ->
    let uu____6465 = get_smtencoding_l_arith_repr ()  in
    uu____6465 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6470  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6475  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6480  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6485  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6490  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6495  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6500  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6505  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6510  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6515  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6522  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6527  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6538  ->
    let uu____6539 = get_using_facts_from ()  in
    match uu____6539 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6575  ->
    let uu____6576 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6576
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6583  ->
    let uu____6584 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6584 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6587 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6594  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6599  ->
    let uu____6600 = get_smt ()  in
    match uu____6600 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6610  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6615  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6620  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6625  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6630  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6635  -> get_use_two_phase_tc () 
let (no_positivity : unit -> Prims.bool) =
  fun uu____6640  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6645  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6650  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6655  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6662 = get_extract ()  in
    match uu____6662 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____6673 =
            let uu____6686 = get_no_extract ()  in
            let uu____6689 = get_extract_namespace ()  in
            let uu____6692 = get_extract_module ()  in
            (uu____6686, uu____6689, uu____6692)  in
          match uu____6673 with
          | ([],[],[]) -> ()
          | uu____6707 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____6753,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6772 -> false  in
          let uu____6781 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6815  ->
                    match uu____6815 with
                    | (path,uu____6823) -> matches_path m_components path))
             in
          match uu____6781 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6834,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6854 = get_extract_namespace ()  in
          match uu____6854 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6870 = get_extract_module ()  in
          match uu____6870 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6882 = no_extract m1  in Prims.op_Negation uu____6882) &&
          (let uu____6884 =
             let uu____6893 = get_extract_namespace ()  in
             let uu____6896 = get_extract_module ()  in
             (uu____6893, uu____6896)  in
           (match uu____6884 with
            | ([],[]) -> true
            | uu____6907 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  