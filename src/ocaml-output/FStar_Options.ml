open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string [@@deriving show]
let uu___is_Low : debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____8 -> false 
let uu___is_Medium : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____12 -> false
  
let uu___is_High : debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____16 -> false 
let uu___is_Extreme : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____20 -> false
  
let uu___is_Other : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____25 -> false
  
let __proj__Other__item___0 : debug_level_t -> Prims.string =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset [@@deriving show]
let uu___is_Bool : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____59 -> false
  
let __proj__Bool__item___0 : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let uu___is_String : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____71 -> false
  
let __proj__String__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0 
let uu___is_Path : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____83 -> false
  
let __proj__Path__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0 
let uu___is_Int : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Int _0 -> true | uu____95 -> false 
let __proj__Int__item___0 : option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0 
let uu___is_List : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____109 -> false
  
let __proj__List__item___0 : option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0 
let uu___is_Unset : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____126 -> false
  
let mk_bool : Prims.bool -> option_val = fun _0_27  -> Bool _0_27 
let mk_string : Prims.string -> option_val = fun _0_28  -> String _0_28 
let mk_path : Prims.string -> option_val = fun _0_29  -> Path _0_29 
let mk_int : Prims.int -> option_val = fun _0_30  -> Int _0_30 
let mk_list : option_val Prims.list -> option_val = fun _0_31  -> List _0_31 
type options =
  | Set 
  | Reset 
  | Restore [@@deriving show]
let uu___is_Set : options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____142 -> false 
let uu___is_Reset : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____146 -> false
  
let uu___is_Restore : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____150 -> false
  
let __unit_tests__ : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let __unit_tests : Prims.unit -> Prims.bool =
  fun uu____162  -> FStar_ST.op_Bang __unit_tests__ 
let __set_unit_tests : Prims.unit -> Prims.unit =
  fun uu____213  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let __clear_unit_tests : Prims.unit -> Prims.unit =
  fun uu____264  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let as_bool : option_val -> Prims.bool =
  fun uu___35_315  ->
    match uu___35_315 with
    | Bool b -> b
    | uu____317 -> failwith "Impos: expected Bool"
  
let as_int : option_val -> Prims.int =
  fun uu___36_320  ->
    match uu___36_320 with
    | Int b -> b
    | uu____322 -> failwith "Impos: expected Int"
  
let as_string : option_val -> Prims.string =
  fun uu___37_325  ->
    match uu___37_325 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____328 -> failwith "Impos: expected String"
  
let as_list' : option_val -> option_val Prims.list =
  fun uu___38_333  ->
    match uu___38_333 with
    | List ts -> ts
    | uu____339 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____345 .
    (option_val -> 'Auu____345) -> option_val -> 'Auu____345 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____361 = as_list' x  in
      FStar_All.pipe_right uu____361 (FStar_List.map as_t)
  
let as_option :
  'Auu____371 .
    (option_val -> 'Auu____371) ->
      option_val -> 'Auu____371 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___39_384  ->
      match uu___39_384 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____388 = as_t v1  in FStar_Pervasives_Native.Some uu____388
  
type optionstate = option_val FStar_Util.smap[@@deriving show]
let fstar_options : optionstate Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let peek : Prims.unit -> optionstate =
  fun uu____406  ->
    let uu____407 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____407
  
let pop : Prims.unit -> Prims.unit =
  fun uu____464  ->
    let uu____465 = FStar_ST.op_Bang fstar_options  in
    match uu____465 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____520::[] -> failwith "TOO MANY POPS!"
    | uu____521::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let push : Prims.unit -> Prims.unit =
  fun uu____579  ->
    let uu____580 =
      let uu____583 =
        let uu____586 = peek ()  in FStar_Util.smap_copy uu____586  in
      let uu____589 = FStar_ST.op_Bang fstar_options  in uu____583 ::
        uu____589
       in
    FStar_ST.op_Colon_Equals fstar_options uu____580
  
let set : optionstate -> Prims.unit =
  fun o  ->
    let uu____703 = FStar_ST.op_Bang fstar_options  in
    match uu____703 with
    | [] -> failwith "set on empty option stack"
    | uu____758::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let set_option : Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____820 = peek ()  in FStar_Util.smap_add uu____820 k v1
  
let set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____829  -> match uu____829 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let light_off_files : Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let add_light_off_file : Prims.string -> Prims.unit =
  fun filename  ->
    let uu____867 =
      let uu____870 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____870
       in
    FStar_ST.op_Colon_Equals light_off_files uu____867
  
let defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("doc", (Bool false));
  ("dump_module", (List []));
  ("eager_inference", (Bool false));
  ("expose_interfaces", (Bool false));
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("fstar_home", Unset);
  ("full_context_dependency", (Bool true));
  ("gen_native_tactics", Unset);
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
  ("no_tactics", (Bool false));
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
  ("split_cases", (Int (Prims.parse_int "0")));
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
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("use_two_phase_tc", (Bool false));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false))] 
let init : Prims.unit -> Prims.unit =
  fun uu____1333  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let clear : Prims.unit -> Prims.unit =
  fun uu____1348  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let _run : Prims.unit = clear () 
let get_option : Prims.string -> option_val =
  fun s  ->
    let uu____1465 =
      let uu____1468 = peek ()  in FStar_Util.smap_try_find uu____1468 s  in
    match uu____1465 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1475 . Prims.string -> (option_val -> 'Auu____1475) -> 'Auu____1475
  = fun s  -> fun c  -> c (get_option s) 
let get_admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____1491  -> lookup_opt "admit_smt_queries" as_bool 
let get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1496  -> lookup_opt "admit_except" (as_option as_string) 
let get_cache_checked_modules : Prims.unit -> Prims.bool =
  fun uu____1501  -> lookup_opt "cache_checked_modules" as_bool 
let get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1506  -> lookup_opt "codegen" (as_option as_string) 
let get_codegen_lib : Prims.unit -> Prims.string Prims.list =
  fun uu____1513  -> lookup_opt "codegen-lib" (as_list as_string) 
let get_debug : Prims.unit -> Prims.string Prims.list =
  fun uu____1520  -> lookup_opt "debug" (as_list as_string) 
let get_debug_level : Prims.unit -> Prims.string Prims.list =
  fun uu____1527  -> lookup_opt "debug_level" (as_list as_string) 
let get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1534  -> lookup_opt "dep" (as_option as_string) 
let get_detail_errors : Prims.unit -> Prims.bool =
  fun uu____1539  -> lookup_opt "detail_errors" as_bool 
let get_detail_hint_replay : Prims.unit -> Prims.bool =
  fun uu____1542  -> lookup_opt "detail_hint_replay" as_bool 
let get_doc : Prims.unit -> Prims.bool =
  fun uu____1545  -> lookup_opt "doc" as_bool 
let get_dump_module : Prims.unit -> Prims.string Prims.list =
  fun uu____1550  -> lookup_opt "dump_module" (as_list as_string) 
let get_eager_inference : Prims.unit -> Prims.bool =
  fun uu____1555  -> lookup_opt "eager_inference" as_bool 
let get_expose_interfaces : Prims.unit -> Prims.bool =
  fun uu____1558  -> lookup_opt "expose_interfaces" as_bool 
let get_extract_module : Prims.unit -> Prims.string Prims.list =
  fun uu____1563  -> lookup_opt "extract_module" (as_list as_string) 
let get_extract_namespace : Prims.unit -> Prims.string Prims.list =
  fun uu____1570  -> lookup_opt "extract_namespace" (as_list as_string) 
let get_fs_typ_app : Prims.unit -> Prims.bool =
  fun uu____1575  -> lookup_opt "fs_typ_app" as_bool 
let get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1580  -> lookup_opt "fstar_home" (as_option as_string) 
let get_gen_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1587  -> lookup_opt "gen_native_tactics" (as_option as_string) 
let get_hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____1592  -> lookup_opt "hide_uvar_nums" as_bool 
let get_hint_info : Prims.unit -> Prims.bool =
  fun uu____1595  -> lookup_opt "hint_info" as_bool 
let get_hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1600  -> lookup_opt "hint_file" (as_option as_string) 
let get_in : Prims.unit -> Prims.bool =
  fun uu____1605  -> lookup_opt "in" as_bool 
let get_ide : Prims.unit -> Prims.bool =
  fun uu____1608  -> lookup_opt "ide" as_bool 
let get_include : Prims.unit -> Prims.string Prims.list =
  fun uu____1613  -> lookup_opt "include" (as_list as_string) 
let get_indent : Prims.unit -> Prims.bool =
  fun uu____1618  -> lookup_opt "indent" as_bool 
let get_initial_fuel : Prims.unit -> Prims.int =
  fun uu____1621  -> lookup_opt "initial_fuel" as_int 
let get_initial_ifuel : Prims.unit -> Prims.int =
  fun uu____1624  -> lookup_opt "initial_ifuel" as_int 
let get_lax : Prims.unit -> Prims.bool =
  fun uu____1627  -> lookup_opt "lax" as_bool 
let get_load : Prims.unit -> Prims.string Prims.list =
  fun uu____1632  -> lookup_opt "load" (as_list as_string) 
let get_log_queries : Prims.unit -> Prims.bool =
  fun uu____1637  -> lookup_opt "log_queries" as_bool 
let get_log_types : Prims.unit -> Prims.bool =
  fun uu____1640  -> lookup_opt "log_types" as_bool 
let get_max_fuel : Prims.unit -> Prims.int =
  fun uu____1643  -> lookup_opt "max_fuel" as_int 
let get_max_ifuel : Prims.unit -> Prims.int =
  fun uu____1646  -> lookup_opt "max_ifuel" as_int 
let get_min_fuel : Prims.unit -> Prims.int =
  fun uu____1649  -> lookup_opt "min_fuel" as_int 
let get_MLish : Prims.unit -> Prims.bool =
  fun uu____1652  -> lookup_opt "MLish" as_bool 
let get_n_cores : Prims.unit -> Prims.int =
  fun uu____1655  -> lookup_opt "n_cores" as_int 
let get_no_default_includes : Prims.unit -> Prims.bool =
  fun uu____1658  -> lookup_opt "no_default_includes" as_bool 
let get_no_extract : Prims.unit -> Prims.string Prims.list =
  fun uu____1663  -> lookup_opt "no_extract" (as_list as_string) 
let get_no_location_info : Prims.unit -> Prims.bool =
  fun uu____1668  -> lookup_opt "no_location_info" as_bool 
let get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1673  -> lookup_opt "odir" (as_option as_string) 
let get_ugly : Prims.unit -> Prims.bool =
  fun uu____1678  -> lookup_opt "ugly" as_bool 
let get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1683  -> lookup_opt "prims" (as_option as_string) 
let get_print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____1688  -> lookup_opt "print_bound_var_types" as_bool 
let get_print_effect_args : Prims.unit -> Prims.bool =
  fun uu____1691  -> lookup_opt "print_effect_args" as_bool 
let get_print_full_names : Prims.unit -> Prims.bool =
  fun uu____1694  -> lookup_opt "print_full_names" as_bool 
let get_print_implicits : Prims.unit -> Prims.bool =
  fun uu____1697  -> lookup_opt "print_implicits" as_bool 
let get_print_universes : Prims.unit -> Prims.bool =
  fun uu____1700  -> lookup_opt "print_universes" as_bool 
let get_print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____1703  -> lookup_opt "print_z3_statistics" as_bool 
let get_prn : Prims.unit -> Prims.bool =
  fun uu____1706  -> lookup_opt "prn" as_bool 
let get_query_stats : Prims.unit -> Prims.bool =
  fun uu____1709  -> lookup_opt "query_stats" as_bool 
let get_record_hints : Prims.unit -> Prims.bool =
  fun uu____1712  -> lookup_opt "record_hints" as_bool 
let get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1717  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let get_silent : Prims.unit -> Prims.bool =
  fun uu____1722  -> lookup_opt "silent" as_bool 
let get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1727  -> lookup_opt "smt" (as_option as_string) 
let get_smtencoding_elim_box : Prims.unit -> Prims.bool =
  fun uu____1732  -> lookup_opt "smtencoding.elim_box" as_bool 
let get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string =
  fun uu____1735  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let get_smtencoding_l_arith_repr : Prims.unit -> Prims.string =
  fun uu____1738  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let get_split_cases : Prims.unit -> Prims.int =
  fun uu____1741  -> lookup_opt "split_cases" as_int 
let get_tactic_trace : Prims.unit -> Prims.bool =
  fun uu____1744  -> lookup_opt "tactic_trace" as_bool 
let get_tactic_trace_d : Prims.unit -> Prims.int =
  fun uu____1747  -> lookup_opt "tactic_trace_d" as_int 
let get_timing : Prims.unit -> Prims.bool =
  fun uu____1750  -> lookup_opt "timing" as_bool 
let get_trace_error : Prims.unit -> Prims.bool =
  fun uu____1753  -> lookup_opt "trace_error" as_bool 
let get_unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____1756  -> lookup_opt "unthrottle_inductives" as_bool 
let get_unsafe_tactic_exec : Prims.unit -> Prims.bool =
  fun uu____1759  -> lookup_opt "unsafe_tactic_exec" as_bool 
let get_use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____1762  -> lookup_opt "use_eq_at_higher_order" as_bool 
let get_use_hints : Prims.unit -> Prims.bool =
  fun uu____1765  -> lookup_opt "use_hints" as_bool 
let get_use_hint_hashes : Prims.unit -> Prims.bool =
  fun uu____1768  -> lookup_opt "use_hint_hashes" as_bool 
let get_use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1773  -> lookup_opt "use_native_tactics" (as_option as_string) 
let get_use_tactics : Prims.unit -> Prims.bool =
  fun uu____1778  ->
    let uu____1779 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1779
  
let get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1786  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let get_verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____1797  -> lookup_opt "verify_module" (as_list as_string) 
let get___temp_no_proj : Prims.unit -> Prims.string Prims.list =
  fun uu____1804  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let get_version : Prims.unit -> Prims.bool =
  fun uu____1809  -> lookup_opt "version" as_bool 
let get_warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____1812  -> lookup_opt "warn_default_effects" as_bool 
let get_z3cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____1817  -> lookup_opt "z3cliopt" (as_list as_string) 
let get_z3refresh : Prims.unit -> Prims.bool =
  fun uu____1822  -> lookup_opt "z3refresh" as_bool 
let get_z3rlimit : Prims.unit -> Prims.int =
  fun uu____1825  -> lookup_opt "z3rlimit" as_int 
let get_z3rlimit_factor : Prims.unit -> Prims.int =
  fun uu____1828  -> lookup_opt "z3rlimit_factor" as_int 
let get_z3seed : Prims.unit -> Prims.int =
  fun uu____1831  -> lookup_opt "z3seed" as_int 
let get_use_two_phase_tc : Prims.unit -> Prims.bool =
  fun uu____1834  -> lookup_opt "use_two_phase_tc" as_bool 
let get_no_positivity : Prims.unit -> Prims.bool =
  fun uu____1837  -> lookup_opt "__no_positivity" as_bool 
let get_ml_no_eta_expand_coertions : Prims.unit -> Prims.bool =
  fun uu____1840  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let dlevel : Prims.string -> debug_level_t =
  fun uu___40_1843  ->
    match uu___40_1843 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1851 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let debug_level_geq : debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1855 = get_debug_level ()  in
    FStar_All.pipe_right uu____1855
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let universe_include_path_base_dirs : Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"] 
let _version : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _platform : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _compiler : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _date : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _commit : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let display_version : Prims.unit -> Prims.unit =
  fun uu____1946  ->
    let uu____1947 =
      let uu____1948 = FStar_ST.op_Bang _version  in
      let uu____1997 = FStar_ST.op_Bang _platform  in
      let uu____2046 = FStar_ST.op_Bang _compiler  in
      let uu____2095 = FStar_ST.op_Bang _date  in
      let uu____2144 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1948
        uu____1997 uu____2046 uu____2095 uu____2144
       in
    FStar_Util.print_string uu____1947
  
let display_usage_aux :
  'Auu____2196 'Auu____2197 .
    ('Auu____2197,Prims.string,'Auu____2196 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2244  ->
         match uu____2244 with
         | (uu____2255,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2266 =
                      let uu____2267 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2267  in
                    FStar_Util.print_string uu____2266
                  else
                    (let uu____2269 =
                       let uu____2270 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2270 doc  in
                     FStar_Util.print_string uu____2269)
              | FStar_Getopt.OneArg (uu____2271,argname) ->
                  if doc = ""
                  then
                    let uu____2277 =
                      let uu____2278 = FStar_Util.colorize_bold flag  in
                      let uu____2279 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2278 uu____2279
                       in
                    FStar_Util.print_string uu____2277
                  else
                    (let uu____2281 =
                       let uu____2282 = FStar_Util.colorize_bold flag  in
                       let uu____2283 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2282
                         uu____2283 doc
                        in
                     FStar_Util.print_string uu____2281))) specs
  
let mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2307 = o  in
    match uu____2307 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2337 =
                let uu____2338 = f ()  in set_option name uu____2338  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2349 = f x  in set_option name uu____2349
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let accumulated_option : Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2363 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2363  in
      mk_list (value :: prev_values)
  
let reverse_accumulated_option : Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2382 =
        let uu____2385 = lookup_opt name as_list'  in
        FStar_List.append uu____2385 [value]  in
      mk_list uu____2382
  
let accumulate_string :
  'Auu____2394 .
    Prims.string ->
      ('Auu____2394 -> Prims.string) -> 'Auu____2394 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2412 =
          let uu____2413 =
            let uu____2414 = post_processor value  in mk_string uu____2414
             in
          accumulated_option name uu____2413  in
        set_option name uu____2412
  
let add_extract_module : Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s 
let add_extract_namespace : Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s 
let add_verify_module : Prims.string -> Prims.unit =
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
  | WithSideEffect of (Prims.unit -> Prims.unit,opt_type)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let uu___is_Const : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2492 -> false
  
let __proj__Const__item___0 : opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0 
let uu___is_IntStr : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2504 -> false
  
let __proj__IntStr__item___0 : opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let uu___is_BoolStr : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2515 -> false
  
let uu___is_PathStr : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2520 -> false
  
let __proj__PathStr__item___0 : opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let uu___is_SimpleStr : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2532 -> false
  
let __proj__SimpleStr__item___0 : opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let uu___is_EnumStr : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2546 -> false
  
let __proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let uu___is_OpenEnumStr : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2570 -> false
  
let __proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let uu___is_PostProcessed : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2606 -> false
  
let __proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let uu___is_Accumulated : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2636 -> false
  
let __proj__Accumulated__item___0 : opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let uu___is_ReverseAccumulated : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2648 -> false
  
let __proj__ReverseAccumulated__item___0 : opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let uu___is_WithSideEffect : opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2666 -> false
  
let __proj__WithSideEffect__item___0 :
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let uu___is_InvalidArgument : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2698 -> true
    | uu____2699 -> false
  
let __proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2706 -> uu____2706
  
let rec parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2720 ->
              let uu____2721 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2721 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2725 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2725
          | PathStr uu____2728 -> mk_path str_val
          | SimpleStr uu____2729 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2734 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2747 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2747
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
            let uu____2764 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2764
  
let rec desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option =
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
    | PostProcessed (uu____2797,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2805,elem_spec) -> desc_of_opt_type elem_spec
  
let rec arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2824 = desc_of_opt_type typ  in
      match uu____2824 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2830  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let pp_validate_dir : option_val -> option_val =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let pp_lowercase : option_val -> option_val =
  fun s  ->
    let uu____2842 =
      let uu____2843 = as_string s  in FStar_String.lowercase uu____2843  in
    mk_string uu____2842
  
let rec specs_with_types :
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2860  ->
    let uu____2871 =
      let uu____2882 =
        let uu____2893 =
          let uu____2902 = let uu____2903 = mk_bool true  in Const uu____2903
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2902,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2904 =
          let uu____2915 =
            let uu____2926 =
              let uu____2937 =
                let uu____2948 =
                  let uu____2959 =
                    let uu____2970 =
                      let uu____2979 =
                        let uu____2980 = mk_bool true  in Const uu____2980
                         in
                      (FStar_Getopt.noshort, "detail_errors", uu____2979,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                       in
                    let uu____2981 =
                      let uu____2992 =
                        let uu____3001 =
                          let uu____3002 = mk_bool true  in Const uu____3002
                           in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____3001,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                         in
                      let uu____3003 =
                        let uu____3014 =
                          let uu____3023 =
                            let uu____3024 = mk_bool true  in
                            Const uu____3024  in
                          (FStar_Getopt.noshort, "doc", uu____3023,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                           in
                        let uu____3025 =
                          let uu____3036 =
                            let uu____3047 =
                              let uu____3056 =
                                let uu____3057 = mk_bool true  in
                                Const uu____3057  in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3056,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                               in
                            let uu____3058 =
                              let uu____3069 =
                                let uu____3080 =
                                  let uu____3091 =
                                    let uu____3100 =
                                      let uu____3101 = mk_bool true  in
                                      Const uu____3101  in
                                    (FStar_Getopt.noshort,
                                      "expose_interfaces", uu____3100,
                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                     in
                                  let uu____3102 =
                                    let uu____3113 =
                                      let uu____3124 =
                                        let uu____3135 =
                                          let uu____3144 =
                                            let uu____3145 = mk_bool true  in
                                            Const uu____3145  in
                                          (FStar_Getopt.noshort,
                                            "hide_uvar_nums", uu____3144,
                                            "Don't print unification variable numbers")
                                           in
                                        let uu____3146 =
                                          let uu____3157 =
                                            let uu____3168 =
                                              let uu____3177 =
                                                let uu____3178 = mk_bool true
                                                   in
                                                Const uu____3178  in
                                              (FStar_Getopt.noshort,
                                                "hint_info", uu____3177,
                                                "Print information regarding hints (deprecated; use --query_stats instead)")
                                               in
                                            let uu____3179 =
                                              let uu____3190 =
                                                let uu____3199 =
                                                  let uu____3200 =
                                                    mk_bool true  in
                                                  Const uu____3200  in
                                                (FStar_Getopt.noshort, "in",
                                                  uu____3199,
                                                  "Legacy interactive mode; reads input from stdin")
                                                 in
                                              let uu____3201 =
                                                let uu____3212 =
                                                  let uu____3221 =
                                                    let uu____3222 =
                                                      mk_bool true  in
                                                    Const uu____3222  in
                                                  (FStar_Getopt.noshort,
                                                    "ide", uu____3221,
                                                    "JSON-based interactive mode for IDEs")
                                                   in
                                                let uu____3223 =
                                                  let uu____3234 =
                                                    let uu____3245 =
                                                      let uu____3254 =
                                                        let uu____3255 =
                                                          mk_bool true  in
                                                        Const uu____3255  in
                                                      (FStar_Getopt.noshort,
                                                        "indent", uu____3254,
                                                        "Parses and outputs the files on the command line")
                                                       in
                                                    let uu____3256 =
                                                      let uu____3267 =
                                                        let uu____3278 =
                                                          let uu____3289 =
                                                            let uu____3298 =
                                                              let uu____3299
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3299
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "lax",
                                                              uu____3298,
                                                              "Run the lax-type checker only (admit all verification conditions)")
                                                             in
                                                          let uu____3300 =
                                                            let uu____3311 =
                                                              let uu____3322
                                                                =
                                                                let uu____3331
                                                                  =
                                                                  let uu____3332
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____3332
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "log_types",
                                                                  uu____3331,
                                                                  "Print types computed for data/val/let-bindings")
                                                                 in
                                                              let uu____3333
                                                                =
                                                                let uu____3344
                                                                  =
                                                                  let uu____3353
                                                                    =
                                                                    let uu____3354
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3354
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3353,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                   in
                                                                let uu____3355
                                                                  =
                                                                  let uu____3366
                                                                    =
                                                                    let uu____3377
                                                                    =
                                                                    let uu____3388
                                                                    =
                                                                    let uu____3399
                                                                    =
                                                                    let uu____3408
                                                                    =
                                                                    let uu____3409
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3409
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3408,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3410
                                                                    =
                                                                    let uu____3421
                                                                    =
                                                                    let uu____3432
                                                                    =
                                                                    let uu____3441
                                                                    =
                                                                    let uu____3442
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3442
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3441,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3443
                                                                    =
                                                                    let uu____3454
                                                                    =
                                                                    let uu____3465
                                                                    =
                                                                    let uu____3474
                                                                    =
                                                                    let uu____3475
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3475
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3474,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3476
                                                                    =
                                                                    let uu____3487
                                                                    =
                                                                    let uu____3498
                                                                    =
                                                                    let uu____3509
                                                                    =
                                                                    let uu____3518
                                                                    =
                                                                    let uu____3519
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3519
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3518,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3520
                                                                    =
                                                                    let uu____3531
                                                                    =
                                                                    let uu____3540
                                                                    =
                                                                    let uu____3541
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3541
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3540,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3542
                                                                    =
                                                                    let uu____3553
                                                                    =
                                                                    let uu____3562
                                                                    =
                                                                    let uu____3563
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3563
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3562,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3564
                                                                    =
                                                                    let uu____3575
                                                                    =
                                                                    let uu____3584
                                                                    =
                                                                    let uu____3585
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3585
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3584,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3586
                                                                    =
                                                                    let uu____3597
                                                                    =
                                                                    let uu____3606
                                                                    =
                                                                    let uu____3607
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3607
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3606,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3608
                                                                    =
                                                                    let uu____3619
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3629
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3628,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3630
                                                                    =
                                                                    let uu____3641
                                                                    =
                                                                    let uu____3650
                                                                    =
                                                                    let uu____3651
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3651
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3650,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3652
                                                                    =
                                                                    let uu____3663
                                                                    =
                                                                    let uu____3672
                                                                    =
                                                                    let uu____3673
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3673
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3672,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3674
                                                                    =
                                                                    let uu____3685
                                                                    =
                                                                    let uu____3694
                                                                    =
                                                                    let uu____3695
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3695
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3694,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3696
                                                                    =
                                                                    let uu____3707
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3727
                                                                    =
                                                                    let uu____3728
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3728
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3727,
                                                                    " ")  in
                                                                    let uu____3729
                                                                    =
                                                                    let uu____3740
                                                                    =
                                                                    let uu____3751
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    let uu____3773
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    let uu____3795
                                                                    =
                                                                    let uu____3804
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3805
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3804,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3806
                                                                    =
                                                                    let uu____3817
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    let uu____3837
                                                                    =
                                                                    let uu____3838
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3838
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3837,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3839
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3859
                                                                    =
                                                                    let uu____3860
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3860
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3859,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3861
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3881
                                                                    =
                                                                    let uu____3882
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3882
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3881,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3894
                                                                    =
                                                                    let uu____3903
                                                                    =
                                                                    let uu____3904
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3904
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3903,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____3905
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3925
                                                                    =
                                                                    let uu____3926
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3926
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3925,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____3927
                                                                    =
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3947
                                                                    =
                                                                    let uu____3948
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3948
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3947,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____3949
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3969
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3970
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3969,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____3971
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    let uu____3992
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3992
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3991,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____3993
                                                                    =
                                                                    let uu____4004
                                                                    =
                                                                    let uu____4015
                                                                    =
                                                                    let uu____4024
                                                                    =
                                                                    let uu____4025
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4025
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4024,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4026
                                                                    =
                                                                    let uu____4037
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4059
                                                                    =
                                                                    let uu____4069
                                                                    =
                                                                    let uu____4070
                                                                    =
                                                                    let uu____4077
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4078
                                                                     in
                                                                    ((fun
                                                                    uu____4083
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4077)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4070
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4069,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4087
                                                                    =
                                                                    let uu____4099
                                                                    =
                                                                    let uu____4108
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4109
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4108,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4110
                                                                    =
                                                                    let uu____4121
                                                                    =
                                                                    let uu____4132
                                                                    =
                                                                    let uu____4141
                                                                    =
                                                                    let uu____4142
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4142
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4141,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4143
                                                                    =
                                                                    let uu____4154
                                                                    =
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4176
                                                                    =
                                                                    let uu____4187
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4208
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4208
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4207,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4209
                                                                    =
                                                                    let uu____4220
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4230
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4230
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4229,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4231
                                                                    =
                                                                    let uu____4242
                                                                    =
                                                                    let uu____4252
                                                                    =
                                                                    let uu____4253
                                                                    =
                                                                    let uu____4260
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4261
                                                                     in
                                                                    ((fun
                                                                    uu____4266
                                                                     ->
                                                                    (
                                                                    let uu____4268
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4268);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4260)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4253
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4252,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4242]
                                                                     in
                                                                    uu____4220
                                                                    ::
                                                                    uu____4231
                                                                     in
                                                                    uu____4198
                                                                    ::
                                                                    uu____4209
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4187
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4176
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4165
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4154
                                                                     in
                                                                    uu____4132
                                                                    ::
                                                                    uu____4143
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4121
                                                                     in
                                                                    uu____4099
                                                                    ::
                                                                    uu____4110
                                                                     in
                                                                    uu____4059
                                                                    ::
                                                                    uu____4087
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4048
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4037
                                                                     in
                                                                    uu____4015
                                                                    ::
                                                                    uu____4026
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4004
                                                                     in
                                                                    uu____3982
                                                                    ::
                                                                    uu____3993
                                                                     in
                                                                    uu____3960
                                                                    ::
                                                                    uu____3971
                                                                     in
                                                                    uu____3938
                                                                    ::
                                                                    uu____3949
                                                                     in
                                                                    uu____3916
                                                                    ::
                                                                    uu____3927
                                                                     in
                                                                    uu____3894
                                                                    ::
                                                                    uu____3905
                                                                     in
                                                                    uu____3872
                                                                    ::
                                                                    uu____3883
                                                                     in
                                                                    uu____3850
                                                                    ::
                                                                    uu____3861
                                                                     in
                                                                    uu____3828
                                                                    ::
                                                                    uu____3839
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3817
                                                                     in
                                                                    uu____3795
                                                                    ::
                                                                    uu____3806
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3784
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3773
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3762
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3751
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3740
                                                                     in
                                                                    uu____3718
                                                                    ::
                                                                    uu____3729
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3707
                                                                     in
                                                                    uu____3685
                                                                    ::
                                                                    uu____3696
                                                                     in
                                                                    uu____3663
                                                                    ::
                                                                    uu____3674
                                                                     in
                                                                    uu____3641
                                                                    ::
                                                                    uu____3652
                                                                     in
                                                                    uu____3619
                                                                    ::
                                                                    uu____3630
                                                                     in
                                                                    uu____3597
                                                                    ::
                                                                    uu____3608
                                                                     in
                                                                    uu____3575
                                                                    ::
                                                                    uu____3586
                                                                     in
                                                                    uu____3553
                                                                    ::
                                                                    uu____3564
                                                                     in
                                                                    uu____3531
                                                                    ::
                                                                    uu____3542
                                                                     in
                                                                    uu____3509
                                                                    ::
                                                                    uu____3520
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3498
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3487
                                                                     in
                                                                    uu____3465
                                                                    ::
                                                                    uu____3476
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3454
                                                                     in
                                                                    uu____3432
                                                                    ::
                                                                    uu____3443
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3421
                                                                     in
                                                                    uu____3399
                                                                    ::
                                                                    uu____3410
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3388
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3377
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3366
                                                                   in
                                                                uu____3344 ::
                                                                  uu____3355
                                                                 in
                                                              uu____3322 ::
                                                                uu____3333
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "load",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "module")),
                                                              "Load compiled module")
                                                              :: uu____3311
                                                             in
                                                          uu____3289 ::
                                                            uu____3300
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "initial_ifuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                          :: uu____3278
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "initial_fuel",
                                                        (IntStr
                                                           "non-negative integer"),
                                                        "Number of unrolling of recursive functions to try initially (default 2)")
                                                        :: uu____3267
                                                       in
                                                    uu____3245 :: uu____3256
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "include",
                                                    (ReverseAccumulated
                                                       (PathStr "path")),
                                                    "A directory in which to search for files included on the command line")
                                                    :: uu____3234
                                                   in
                                                uu____3212 :: uu____3223  in
                                              uu____3190 :: uu____3201  in
                                            uu____3168 :: uu____3179  in
                                          (FStar_Getopt.noshort, "hint_file",
                                            (PathStr "path"),
                                            "Read/write hints to <path> (instead of module-specific hints files)")
                                            :: uu____3157
                                           in
                                        uu____3135 :: uu____3146  in
                                      (FStar_Getopt.noshort,
                                        "gen_native_tactics",
                                        (PathStr "[path]"),
                                        "Compile all user tactics used in the module in <path>")
                                        :: uu____3124
                                       in
                                    (FStar_Getopt.noshort, "fstar_home",
                                      (PathStr "dir"),
                                      "Set the FSTAR_HOME variable to <dir>")
                                      :: uu____3113
                                     in
                                  uu____3091 :: uu____3102  in
                                (FStar_Getopt.noshort, "extract_namespace",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "namespace name")))),
                                  "Only extract modules in the specified namespace")
                                  :: uu____3080
                                 in
                              (FStar_Getopt.noshort, "extract_module",
                                (Accumulated
                                   (PostProcessed
                                      (pp_lowercase,
                                        (SimpleStr "module_name")))),
                                "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                :: uu____3069
                               in
                            uu____3047 :: uu____3058  in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3036
                           in
                        uu____3014 :: uu____3025  in
                      uu____2992 :: uu____3003  in
                    uu____2970 :: uu____2981  in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2959
                   in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2948
                 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2937
               in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2926
             in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2915
           in
        uu____2893 :: uu____2904  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2882
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2871

and specs : Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4958  ->
    let uu____4961 = specs_with_types ()  in
    FStar_List.map
      (fun uu____4986  ->
         match uu____4986 with
         | (short,long,typ,doc) ->
             let uu____4999 =
               let uu____5010 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5010, doc)  in
             mk_spec uu____4999) uu____4961

let settable : Prims.string -> Prims.bool =
  fun uu___41_5017  ->
    match uu___41_5017 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
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
    | "split_cases" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "no_tactics" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | uu____5018 -> false
  
let resettable : Prims.string -> Prims.bool =
  fun s  ->
    (((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
      (s = "using_facts_from")
  
let all_specs : FStar_Getopt.opt Prims.list = specs () 
let all_specs_with_types :
  (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list
  = specs_with_types () 
let settable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5075  ->
          match uu____5075 with
          | (uu____5086,x,uu____5088,uu____5089) -> settable x))
  
let resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5135  ->
          match uu____5135 with
          | (uu____5146,x,uu____5148,uu____5149) -> resettable x))
  
let display_usage : Prims.unit -> Prims.unit =
  fun uu____5156  ->
    let uu____5157 = specs ()  in display_usage_aux uu____5157
  
let fstar_home : Prims.unit -> Prims.string =
  fun uu____5172  ->
    let uu____5173 = get_fstar_home ()  in
    match uu____5173 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5179 =
            let uu____5184 = mk_string x1  in ("fstar_home", uu____5184)  in
          set_option' uu____5179);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let uu___is_File_argument : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5192 -> true
    | uu____5193 -> false
  
let __proj__File_argument__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5200 -> uu____5200
  
let set_options : options -> Prims.string -> FStar_Getopt.parse_cmdline_res =
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
          let uu____5244 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5244
  
let file_list_ : Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5266  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5271 =
             let uu____5274 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5274 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5271)
       in
    let uu____5381 =
      let uu____5384 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5384
       in
    (res, uu____5381)
  
let file_list : Prims.unit -> Prims.string Prims.list =
  fun uu____5445  -> FStar_ST.op_Bang file_list_ 
let restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5507 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5507 (fun x  -> ())  in
     (let uu____5513 =
        let uu____5518 =
          let uu____5519 = FStar_List.map mk_string old_verify_module  in
          List uu____5519  in
        ("verify_module", uu____5518)  in
      set_option' uu____5513);
     r)
  
let module_name_of_file_name : Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5527 =
        let uu____5528 =
          let uu____5529 =
            let uu____5530 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5530  in
          (FStar_String.length f1) - uu____5529  in
        uu____5528 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5527  in
    FStar_String.lowercase f2
  
let should_verify : Prims.string -> Prims.bool =
  fun m  ->
    let uu____5534 = get_lax ()  in
    if uu____5534
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let should_verify_file : Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5542 = module_name_of_file_name fn  in should_verify uu____5542
  
let dont_gen_projectors : Prims.string -> Prims.bool =
  fun m  ->
    let uu____5546 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5546
  
let should_print_message : Prims.string -> Prims.bool =
  fun m  ->
    let uu____5552 = should_verify m  in
    if uu____5552 then m <> "Prims" else false
  
let include_path : Prims.unit -> Prims.string Prims.list =
  fun uu____5558  ->
    let uu____5559 = get_no_default_includes ()  in
    if uu____5559
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5567 =
         let uu____5570 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5570
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5583 =
         let uu____5586 = get_include ()  in
         FStar_List.append uu____5586 ["."]  in
       FStar_List.append uu____5567 uu____5583)
  
let find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5594 = FStar_Util.is_path_absolute filename  in
    if uu____5594
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5601 =
         let uu____5604 = include_path ()  in FStar_List.rev uu____5604  in
       FStar_Util.find_map uu____5601
         (fun p  ->
            let path = FStar_Util.join_paths p filename  in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let prims : Prims.unit -> Prims.string =
  fun uu____5616  ->
    let uu____5617 = get_prims ()  in
    match uu____5617 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5621 = find_file filename  in
        (match uu____5621 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5625 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5625)
    | FStar_Pervasives_Native.Some x -> x
  
let prims_basename : Prims.unit -> Prims.string =
  fun uu____5629  ->
    let uu____5630 = prims ()  in FStar_Util.basename uu____5630
  
let pervasives : Prims.unit -> Prims.string =
  fun uu____5633  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5635 = find_file filename  in
    match uu____5635 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5639 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5639
  
let pervasives_basename : Prims.unit -> Prims.string =
  fun uu____5642  ->
    let uu____5643 = pervasives ()  in FStar_Util.basename uu____5643
  
let pervasives_native_basename : Prims.unit -> Prims.string =
  fun uu____5646  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5648 = find_file filename  in
    match uu____5648 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5652 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5652
  
let prepend_output_dir : Prims.string -> Prims.string =
  fun fname  ->
    let uu____5656 = get_odir ()  in
    match uu____5656 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
  
let __temp_no_proj : Prims.string -> Prims.bool =
  fun s  ->
    let uu____5663 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5663 (FStar_List.contains s)
  
let admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____5670  -> get_admit_smt_queries () 
let admit_except : Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5675  -> get_admit_except () 
let cache_checked_modules : Prims.unit -> Prims.bool =
  fun uu____5678  -> get_cache_checked_modules () 
let codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5683  -> get_codegen () 
let codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5690  ->
    let uu____5691 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____5691
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let debug_any : Prims.unit -> Prims.bool =
  fun uu____5706  -> let uu____5707 = get_debug ()  in uu____5707 <> [] 
let debug_at_level : Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5720 = get_debug ()  in
       FStar_All.pipe_right uu____5720 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5729  -> get_dep () 
let detail_errors : Prims.unit -> Prims.bool =
  fun uu____5732  -> get_detail_errors () 
let detail_hint_replay : Prims.unit -> Prims.bool =
  fun uu____5735  -> get_detail_hint_replay () 
let doc : Prims.unit -> Prims.bool = fun uu____5738  -> get_doc () 
let dump_module : Prims.string -> Prims.bool =
  fun s  ->
    let uu____5742 = get_dump_module ()  in
    FStar_All.pipe_right uu____5742 (FStar_List.contains s)
  
let eager_inference : Prims.unit -> Prims.bool =
  fun uu____5749  -> get_eager_inference () 
let expose_interfaces : Prims.unit -> Prims.bool =
  fun uu____5752  -> get_expose_interfaces () 
let fs_typ_app : Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5756 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____5756
  
let gen_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5815  -> get_gen_native_tactics () 
let full_context_dependency : Prims.unit -> Prims.bool =
  fun uu____5818  -> true 
let hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____5821  -> get_hide_uvar_nums () 
let hint_info : Prims.unit -> Prims.bool =
  fun uu____5824  -> (get_hint_info ()) || (get_query_stats ()) 
let hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5829  -> get_hint_file () 
let ide : Prims.unit -> Prims.bool = fun uu____5832  -> get_ide () 
let indent : Prims.unit -> Prims.bool = fun uu____5835  -> get_indent () 
let initial_fuel : Prims.unit -> Prims.int =
  fun uu____5838  ->
    let uu____5839 = get_initial_fuel ()  in
    let uu____5840 = get_max_fuel ()  in Prims.min uu____5839 uu____5840
  
let initial_ifuel : Prims.unit -> Prims.int =
  fun uu____5843  ->
    let uu____5844 = get_initial_ifuel ()  in
    let uu____5845 = get_max_ifuel ()  in Prims.min uu____5844 uu____5845
  
let interactive : Prims.unit -> Prims.bool =
  fun uu____5848  -> (get_in ()) || (get_ide ()) 
let lax : Prims.unit -> Prims.bool = fun uu____5851  -> get_lax () 
let load : Prims.unit -> Prims.string Prims.list =
  fun uu____5856  -> get_load () 
let legacy_interactive : Prims.unit -> Prims.bool =
  fun uu____5859  -> get_in () 
let log_queries : Prims.unit -> Prims.bool =
  fun uu____5862  -> get_log_queries () 
let log_types : Prims.unit -> Prims.bool =
  fun uu____5865  -> get_log_types () 
let max_fuel : Prims.unit -> Prims.int = fun uu____5868  -> get_max_fuel () 
let max_ifuel : Prims.unit -> Prims.int = fun uu____5871  -> get_max_ifuel () 
let min_fuel : Prims.unit -> Prims.int = fun uu____5874  -> get_min_fuel () 
let ml_ish : Prims.unit -> Prims.bool = fun uu____5877  -> get_MLish () 
let set_ml_ish : Prims.unit -> Prims.unit =
  fun uu____5880  -> set_option "MLish" (Bool true) 
let n_cores : Prims.unit -> Prims.int = fun uu____5883  -> get_n_cores () 
let no_default_includes : Prims.unit -> Prims.bool =
  fun uu____5886  -> get_no_default_includes () 
let no_extract : Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____5891 = get_no_extract ()  in
    FStar_All.pipe_right uu____5891
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let no_location_info : Prims.unit -> Prims.bool =
  fun uu____5900  -> get_no_location_info () 
let output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5905  -> get_odir () 
let ugly : Prims.unit -> Prims.bool = fun uu____5908  -> get_ugly () 
let print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____5911  -> get_print_bound_var_types () 
let print_effect_args : Prims.unit -> Prims.bool =
  fun uu____5914  -> get_print_effect_args () 
let print_implicits : Prims.unit -> Prims.bool =
  fun uu____5917  -> get_print_implicits () 
let print_real_names : Prims.unit -> Prims.bool =
  fun uu____5920  -> (get_prn ()) || (get_print_full_names ()) 
let print_universes : Prims.unit -> Prims.bool =
  fun uu____5923  -> get_print_universes () 
let print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____5926  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let query_stats : Prims.unit -> Prims.bool =
  fun uu____5929  -> get_query_stats () 
let record_hints : Prims.unit -> Prims.bool =
  fun uu____5932  -> get_record_hints () 
let reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5937  -> get_reuse_hint_for () 
let silent : Prims.unit -> Prims.bool = fun uu____5940  -> get_silent () 
let smtencoding_elim_box : Prims.unit -> Prims.bool =
  fun uu____5943  -> get_smtencoding_elim_box () 
let smtencoding_nl_arith_native : Prims.unit -> Prims.bool =
  fun uu____5946  ->
    let uu____5947 = get_smtencoding_nl_arith_repr ()  in
    uu____5947 = "native"
  
let smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool =
  fun uu____5950  ->
    let uu____5951 = get_smtencoding_nl_arith_repr ()  in
    uu____5951 = "wrapped"
  
let smtencoding_nl_arith_default : Prims.unit -> Prims.bool =
  fun uu____5954  ->
    let uu____5955 = get_smtencoding_nl_arith_repr ()  in
    uu____5955 = "boxwrap"
  
let smtencoding_l_arith_native : Prims.unit -> Prims.bool =
  fun uu____5958  ->
    let uu____5959 = get_smtencoding_l_arith_repr ()  in
    uu____5959 = "native"
  
let smtencoding_l_arith_default : Prims.unit -> Prims.bool =
  fun uu____5962  ->
    let uu____5963 = get_smtencoding_l_arith_repr ()  in
    uu____5963 = "boxwrap"
  
let split_cases : Prims.unit -> Prims.int =
  fun uu____5966  -> get_split_cases () 
let tactic_trace : Prims.unit -> Prims.bool =
  fun uu____5969  -> get_tactic_trace () 
let tactic_trace_d : Prims.unit -> Prims.int =
  fun uu____5972  -> get_tactic_trace_d () 
let timing : Prims.unit -> Prims.bool = fun uu____5975  -> get_timing () 
let trace_error : Prims.unit -> Prims.bool =
  fun uu____5978  -> get_trace_error () 
let unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____5981  -> get_unthrottle_inductives () 
let unsafe_tactic_exec : Prims.unit -> Prims.bool =
  fun uu____5984  -> get_unsafe_tactic_exec () 
let use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____5987  -> get_use_eq_at_higher_order () 
let use_hints : Prims.unit -> Prims.bool =
  fun uu____5990  -> get_use_hints () 
let use_hint_hashes : Prims.unit -> Prims.bool =
  fun uu____5993  -> get_use_hint_hashes () 
let use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5998  -> get_use_native_tactics () 
let use_tactics : Prims.unit -> Prims.bool =
  fun uu____6001  -> get_use_tactics () 
let using_facts_from :
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6010  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____6039 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____6039  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((FStar_Ident.path_of_text s1), true))
       in
    let parse_setting s =
      FStar_All.pipe_right (FStar_Util.split s " ")
        (FStar_List.map parse_one_setting)
       in
    let uu____6075 = get_using_facts_from ()  in
    match uu____6075 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6107 = FStar_List.collect parse_setting ns  in
        FStar_All.pipe_right uu____6107 FStar_List.rev
  
let warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____6146  -> get_warn_default_effects () 
let z3_exe : Prims.unit -> Prims.string =
  fun uu____6149  ->
    let uu____6150 = get_smt ()  in
    match uu____6150 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let z3_cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____6158  -> get_z3cliopt () 
let z3_refresh : Prims.unit -> Prims.bool =
  fun uu____6161  -> get_z3refresh () 
let z3_rlimit : Prims.unit -> Prims.int = fun uu____6164  -> get_z3rlimit () 
let z3_rlimit_factor : Prims.unit -> Prims.int =
  fun uu____6167  -> get_z3rlimit_factor () 
let z3_seed : Prims.unit -> Prims.int = fun uu____6170  -> get_z3seed () 
let use_two_phase_tc : Prims.unit -> Prims.bool =
  fun uu____6173  -> get_use_two_phase_tc () 
let no_positivity : Prims.unit -> Prims.bool =
  fun uu____6176  -> get_no_positivity () 
let ml_no_eta_expand_coertions : Prims.unit -> Prims.bool =
  fun uu____6179  -> get_ml_no_eta_expand_coertions () 
let should_extract_namespace : Prims.string -> Prims.bool =
  fun m  ->
    let uu____6183 = get_extract_namespace ()  in
    match uu____6183 with
    | [] -> false
    | ns ->
        FStar_All.pipe_right ns
          (FStar_Util.for_some
             (fun n1  -> FStar_Util.starts_with m (FStar_String.lowercase n1)))
  
let should_extract_module : Prims.string -> Prims.bool =
  fun m  ->
    let uu____6196 = get_extract_module ()  in
    match uu____6196 with
    | [] -> false
    | l ->
        FStar_All.pipe_right l
          (FStar_Util.for_some (fun n1  -> (FStar_String.lowercase n1) = m))
  
let should_extract : Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    (let uu____6212 = no_extract m1  in Prims.op_Negation uu____6212) &&
      (let uu____6214 =
         let uu____6223 = get_extract_namespace ()  in
         let uu____6226 = get_extract_module ()  in (uu____6223, uu____6226)
          in
       match uu____6214 with
       | ([],[]) -> true
       | uu____6237 ->
           (should_extract_namespace m1) || (should_extract_module m1))
  
let codegen_fsharp : Prims.unit -> Prims.bool =
  fun uu____6248  ->
    let uu____6249 = codegen ()  in
    uu____6249 = (FStar_Pervasives_Native.Some "FSharp")
  