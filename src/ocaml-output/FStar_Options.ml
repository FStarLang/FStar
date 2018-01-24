open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string [@@deriving show]
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____8 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____12 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____16 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____20 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____25 -> false
  
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
    match projectee with | Bool _0 -> true | uu____59 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____71 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____83 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____95 -> false 
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____109 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____126 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_27  -> Bool _0_27 
let (mk_string : Prims.string -> option_val) = fun _0_28  -> String _0_28 
let (mk_path : Prims.string -> option_val) = fun _0_29  -> Path _0_29 
let (mk_int : Prims.int -> option_val) = fun _0_30  -> Int _0_30 
let (mk_list : option_val Prims.list -> option_val) =
  fun _0_31  -> List _0_31 
type options =
  | Set 
  | Reset 
  | Restore [@@deriving show]
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____142 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____146 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____150 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : Prims.unit -> Prims.bool) =
  fun uu____166  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : Prims.unit -> Prims.unit) =
  fun uu____188  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : Prims.unit -> Prims.unit) =
  fun uu____210  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___34_232  ->
    match uu___34_232 with
    | Bool b -> b
    | uu____234 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___35_237  ->
    match uu___35_237 with
    | Int b -> b
    | uu____239 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___36_242  ->
    match uu___36_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___37_250  ->
    match uu___37_250 with
    | List ts -> ts
    | uu____256 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____262 .
    (option_val -> 'Auu____262) -> option_val -> 'Auu____262 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____278 = as_list' x  in
      FStar_All.pipe_right uu____278 (FStar_List.map as_t)
  
let as_option :
  'Auu____288 .
    (option_val -> 'Auu____288) ->
      option_val -> 'Auu____288 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___38_301  ->
      match uu___38_301 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____305 = as_t v1  in FStar_Pervasives_Native.Some uu____305
  
type optionstate = option_val FStar_Util.smap[@@deriving show]
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : Prims.unit -> optionstate) =
  fun uu____327  ->
    let uu____328 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____328
  
let (pop : Prims.unit -> Prims.unit) =
  fun uu____356  ->
    let uu____357 = FStar_ST.op_Bang fstar_options  in
    match uu____357 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____383::[] -> failwith "TOO MANY POPS!"
    | uu____384::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : Prims.unit -> Prims.unit) =
  fun uu____413  ->
    let uu____414 =
      let uu____417 =
        let uu____420 = peek ()  in FStar_Util.smap_copy uu____420  in
      let uu____423 = FStar_ST.op_Bang fstar_options  in uu____417 ::
        uu____423
       in
    FStar_ST.op_Colon_Equals fstar_options uu____414
  
let (set : optionstate -> Prims.unit) =
  fun o  ->
    let uu____479 = FStar_ST.op_Bang fstar_options  in
    match uu____479 with
    | [] -> failwith "set on empty option stack"
    | uu____505::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (set_option : Prims.string -> option_val -> Prims.unit) =
  fun k  ->
    fun v1  -> let uu____538 = peek ()  in FStar_Util.smap_add uu____538 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit) =
  fun uu____547  -> match uu____547 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> Prims.unit) =
  fun filename  ->
    let uu____589 =
      let uu____592 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____592
       in
    FStar_ST.op_Colon_Equals light_off_files uu____589
  
let (defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
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
  ("extract", Unset);
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
  ("warn_error", (String ""))] 
let (init : Prims.unit -> Prims.unit) =
  fun uu____1009  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : Prims.unit -> Prims.unit) =
  fun uu____1024  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : Prims.unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1083 =
      let uu____1086 = peek ()  in FStar_Util.smap_try_find uu____1086 s  in
    match uu____1083 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1093 . Prims.string -> (option_val -> 'Auu____1093) -> 'Auu____1093
  = fun s  -> fun c  -> c (get_option s) 
let (get_admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____1109  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1114  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____1119  -> lookup_opt "cache_checked_modules" as_bool 
let (get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1124  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : Prims.unit -> Prims.string Prims.list) =
  fun uu____1131  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : Prims.unit -> Prims.string Prims.list) =
  fun uu____1138  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : Prims.unit -> Prims.string Prims.list) =
  fun uu____1145  -> lookup_opt "debug_level" (as_list as_string) 
let (get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1152  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : Prims.unit -> Prims.bool) =
  fun uu____1157  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____1160  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : Prims.unit -> Prims.bool) =
  fun uu____1163  -> lookup_opt "doc" as_bool 
let (get_dump_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1168  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : Prims.unit -> Prims.bool) =
  fun uu____1173  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1176  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1183  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1194  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : Prims.unit -> Prims.string Prims.list) =
  fun uu____1201  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : Prims.unit -> Prims.bool) =
  fun uu____1206  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1211  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_gen_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1218  -> lookup_opt "gen_native_tactics" (as_option as_string) 
let (get_hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____1223  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : Prims.unit -> Prims.bool) =
  fun uu____1226  -> lookup_opt "hint_info" as_bool 
let (get_hint_file :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1231  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : Prims.unit -> Prims.bool) =
  fun uu____1236  -> lookup_opt "in" as_bool 
let (get_ide : Prims.unit -> Prims.bool) =
  fun uu____1239  -> lookup_opt "ide" as_bool 
let (get_include : Prims.unit -> Prims.string Prims.list) =
  fun uu____1244  -> lookup_opt "include" (as_list as_string) 
let (get_indent : Prims.unit -> Prims.bool) =
  fun uu____1249  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : Prims.unit -> Prims.int) =
  fun uu____1252  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____1255  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : Prims.unit -> Prims.bool) =
  fun uu____1258  -> lookup_opt "lax" as_bool 
let (get_load : Prims.unit -> Prims.string Prims.list) =
  fun uu____1263  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : Prims.unit -> Prims.bool) =
  fun uu____1268  -> lookup_opt "log_queries" as_bool 
let (get_log_types : Prims.unit -> Prims.bool) =
  fun uu____1271  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : Prims.unit -> Prims.int) =
  fun uu____1274  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : Prims.unit -> Prims.int) =
  fun uu____1277  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : Prims.unit -> Prims.int) =
  fun uu____1280  -> lookup_opt "min_fuel" as_int 
let (get_MLish : Prims.unit -> Prims.bool) =
  fun uu____1283  -> lookup_opt "MLish" as_bool 
let (get_n_cores : Prims.unit -> Prims.int) =
  fun uu____1286  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____1289  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : Prims.unit -> Prims.string Prims.list) =
  fun uu____1294  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : Prims.unit -> Prims.bool) =
  fun uu____1299  -> lookup_opt "no_location_info" as_bool 
let (get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1304  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : Prims.unit -> Prims.bool) =
  fun uu____1309  -> lookup_opt "ugly" as_bool 
let (get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1314  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____1319  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____1322  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : Prims.unit -> Prims.bool) =
  fun uu____1325  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : Prims.unit -> Prims.bool) =
  fun uu____1328  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : Prims.unit -> Prims.bool) =
  fun uu____1331  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____1334  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : Prims.unit -> Prims.bool) =
  fun uu____1337  -> lookup_opt "prn" as_bool 
let (get_query_stats : Prims.unit -> Prims.bool) =
  fun uu____1340  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : Prims.unit -> Prims.bool) =
  fun uu____1343  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1348  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : Prims.unit -> Prims.bool) =
  fun uu____1353  -> lookup_opt "silent" as_bool 
let (get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1358  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____1363  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1366  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1369  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____1372  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____1375  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____1378  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : Prims.unit -> Prims.bool) =
  fun uu____1381  -> lookup_opt "timing" as_bool 
let (get_trace_error : Prims.unit -> Prims.bool) =
  fun uu____1384  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____1387  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____1390  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____1393  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : Prims.unit -> Prims.bool) =
  fun uu____1396  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____1399  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1404  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : Prims.unit -> Prims.bool) =
  fun uu____1409  ->
    let uu____1410 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1410
  
let (get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1417  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1428  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1435  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : Prims.unit -> Prims.string Prims.list) =
  fun uu____1442  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : Prims.unit -> Prims.bool) =
  fun uu____1447  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____1450  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____1455  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : Prims.unit -> Prims.bool) =
  fun uu____1460  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : Prims.unit -> Prims.int) =
  fun uu____1463  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____1466  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : Prims.unit -> Prims.int) =
  fun uu____1469  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____1472  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : Prims.unit -> Prims.bool) =
  fun uu____1475  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____1478  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : Prims.unit -> Prims.string) =
  fun uu____1481  -> lookup_opt "warn_error" as_string 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___39_1484  ->
    match uu___39_1484 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1492 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1496 = get_debug_level ()  in
    FStar_All.pipe_right uu____1496
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : Prims.unit -> Prims.unit) =
  fun uu____1627  ->
    let uu____1628 =
      let uu____1629 = FStar_ST.op_Bang _version  in
      let uu____1649 = FStar_ST.op_Bang _platform  in
      let uu____1669 = FStar_ST.op_Bang _compiler  in
      let uu____1689 = FStar_ST.op_Bang _date  in
      let uu____1709 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1629
        uu____1649 uu____1669 uu____1689 uu____1709
       in
    FStar_Util.print_string uu____1628
  
let display_usage_aux :
  'Auu____1732 'Auu____1733 .
    ('Auu____1733,Prims.string,'Auu____1732 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1780  ->
         match uu____1780 with
         | (uu____1791,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1802 =
                      let uu____1803 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____1803  in
                    FStar_Util.print_string uu____1802
                  else
                    (let uu____1805 =
                       let uu____1806 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____1806 doc  in
                     FStar_Util.print_string uu____1805)
              | FStar_Getopt.OneArg (uu____1807,argname) ->
                  if doc = ""
                  then
                    let uu____1813 =
                      let uu____1814 = FStar_Util.colorize_bold flag  in
                      let uu____1815 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____1814 uu____1815
                       in
                    FStar_Util.print_string uu____1813
                  else
                    (let uu____1817 =
                       let uu____1818 = FStar_Util.colorize_bold flag  in
                       let uu____1819 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1818
                         uu____1819 doc
                        in
                     FStar_Util.print_string uu____1817))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____1843 = o  in
    match uu____1843 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1873 =
                let uu____1874 = f ()  in set_option name uu____1874  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1885 = f x  in set_option name uu____1885
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1899 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____1899  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____1918 =
        let uu____1921 = lookup_opt name as_list'  in
        FStar_List.append uu____1921 [value]  in
      mk_list uu____1918
  
let accumulate_string :
  'Auu____1930 .
    Prims.string ->
      ('Auu____1930 -> Prims.string) -> 'Auu____1930 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1948 =
          let uu____1949 =
            let uu____1950 = post_processor value  in mk_string uu____1950
             in
          accumulated_option name uu____1949  in
        set_option name uu____1948
  
let (add_extract_module : Prims.string -> Prims.unit) =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s 
let (add_extract_namespace : Prims.string -> Prims.unit) =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s 
let (add_verify_module : Prims.string -> Prims.unit) =
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
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2028 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2040 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2051 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2056 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2068 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2082 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2106 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2142 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2172 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2184 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2202 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2234 -> true
    | uu____2235 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2242 -> uu____2242
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2256 ->
              let uu____2257 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2257 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2261 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2261
          | PathStr uu____2264 -> mk_path str_val
          | SimpleStr uu____2265 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2270 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2283 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2283
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
            let uu____2300 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2300
  
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
    | PostProcessed (uu____2333,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2341,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2360 = desc_of_opt_type typ  in
      match uu____2360 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2366  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2378 =
      let uu____2379 = as_string s  in FStar_String.lowercase uu____2379  in
    mk_string uu____2378
  
let rec (specs_with_types :
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2396  ->
    let uu____2407 =
      let uu____2418 =
        let uu____2429 =
          let uu____2438 = let uu____2439 = mk_bool true  in Const uu____2439
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2438,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2440 =
          let uu____2451 =
            let uu____2462 =
              let uu____2473 =
                let uu____2484 =
                  let uu____2495 =
                    let uu____2506 =
                      let uu____2515 =
                        let uu____2516 = mk_bool true  in Const uu____2516
                         in
                      (FStar_Getopt.noshort, "detail_errors", uu____2515,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                       in
                    let uu____2517 =
                      let uu____2528 =
                        let uu____2537 =
                          let uu____2538 = mk_bool true  in Const uu____2538
                           in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2537,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                         in
                      let uu____2539 =
                        let uu____2550 =
                          let uu____2559 =
                            let uu____2560 = mk_bool true  in
                            Const uu____2560  in
                          (FStar_Getopt.noshort, "doc", uu____2559,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                           in
                        let uu____2561 =
                          let uu____2572 =
                            let uu____2583 =
                              let uu____2592 =
                                let uu____2593 = mk_bool true  in
                                Const uu____2593  in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____2592,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                               in
                            let uu____2594 =
                              let uu____2605 =
                                let uu____2616 =
                                  let uu____2627 =
                                    let uu____2638 =
                                      let uu____2647 =
                                        let uu____2648 = mk_bool true  in
                                        Const uu____2648  in
                                      (FStar_Getopt.noshort,
                                        "expose_interfaces", uu____2647,
                                        "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                       in
                                    let uu____2649 =
                                      let uu____2660 =
                                        let uu____2671 =
                                          let uu____2682 =
                                            let uu____2691 =
                                              let uu____2692 = mk_bool true
                                                 in
                                              Const uu____2692  in
                                            (FStar_Getopt.noshort,
                                              "hide_uvar_nums", uu____2691,
                                              "Don't print unification variable numbers")
                                             in
                                          let uu____2693 =
                                            let uu____2704 =
                                              let uu____2715 =
                                                let uu____2724 =
                                                  let uu____2725 =
                                                    mk_bool true  in
                                                  Const uu____2725  in
                                                (FStar_Getopt.noshort,
                                                  "hint_info", uu____2724,
                                                  "Print information regarding hints (deprecated; use --query_stats instead)")
                                                 in
                                              let uu____2726 =
                                                let uu____2737 =
                                                  let uu____2746 =
                                                    let uu____2747 =
                                                      mk_bool true  in
                                                    Const uu____2747  in
                                                  (FStar_Getopt.noshort,
                                                    "in", uu____2746,
                                                    "Legacy interactive mode; reads input from stdin")
                                                   in
                                                let uu____2748 =
                                                  let uu____2759 =
                                                    let uu____2768 =
                                                      let uu____2769 =
                                                        mk_bool true  in
                                                      Const uu____2769  in
                                                    (FStar_Getopt.noshort,
                                                      "ide", uu____2768,
                                                      "JSON-based interactive mode for IDEs")
                                                     in
                                                  let uu____2770 =
                                                    let uu____2781 =
                                                      let uu____2792 =
                                                        let uu____2801 =
                                                          let uu____2802 =
                                                            mk_bool true  in
                                                          Const uu____2802
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "indent",
                                                          uu____2801,
                                                          "Parses and outputs the files on the command line")
                                                         in
                                                      let uu____2803 =
                                                        let uu____2814 =
                                                          let uu____2825 =
                                                            let uu____2836 =
                                                              let uu____2845
                                                                =
                                                                let uu____2846
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____2846
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "lax",
                                                                uu____2845,
                                                                "Run the lax-type checker only (admit all verification conditions)")
                                                               in
                                                            let uu____2847 =
                                                              let uu____2858
                                                                =
                                                                let uu____2869
                                                                  =
                                                                  let uu____2878
                                                                    =
                                                                    let uu____2879
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2879
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2878,
                                                                    "Print types computed for data/val/let-bindings")
                                                                   in
                                                                let uu____2880
                                                                  =
                                                                  let uu____2891
                                                                    =
                                                                    let uu____2900
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2901
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2900,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                  let uu____2902
                                                                    =
                                                                    let uu____2913
                                                                    =
                                                                    let uu____2924
                                                                    =
                                                                    let uu____2935
                                                                    =
                                                                    let uu____2946
                                                                    =
                                                                    let uu____2955
                                                                    =
                                                                    let uu____2956
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2955,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____2957
                                                                    =
                                                                    let uu____2968
                                                                    =
                                                                    let uu____2979
                                                                    =
                                                                    let uu____2988
                                                                    =
                                                                    let uu____2989
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2989
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____2988,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____2990
                                                                    =
                                                                    let uu____3001
                                                                    =
                                                                    let uu____3012
                                                                    =
                                                                    let uu____3021
                                                                    =
                                                                    let uu____3022
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3022
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3021,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3023
                                                                    =
                                                                    let uu____3034
                                                                    =
                                                                    let uu____3045
                                                                    =
                                                                    let uu____3056
                                                                    =
                                                                    let uu____3065
                                                                    =
                                                                    let uu____3066
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3065,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3067
                                                                    =
                                                                    let uu____3078
                                                                    =
                                                                    let uu____3087
                                                                    =
                                                                    let uu____3088
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3088
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3087,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3089
                                                                    =
                                                                    let uu____3100
                                                                    =
                                                                    let uu____3109
                                                                    =
                                                                    let uu____3110
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3110
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3109,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3111
                                                                    =
                                                                    let uu____3122
                                                                    =
                                                                    let uu____3131
                                                                    =
                                                                    let uu____3132
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3132
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3131,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3133
                                                                    =
                                                                    let uu____3144
                                                                    =
                                                                    let uu____3153
                                                                    =
                                                                    let uu____3154
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3154
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3153,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3155
                                                                    =
                                                                    let uu____3166
                                                                    =
                                                                    let uu____3175
                                                                    =
                                                                    let uu____3176
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3176
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3175,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3177
                                                                    =
                                                                    let uu____3188
                                                                    =
                                                                    let uu____3197
                                                                    =
                                                                    let uu____3198
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3198
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3197,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3199
                                                                    =
                                                                    let uu____3210
                                                                    =
                                                                    let uu____3219
                                                                    =
                                                                    let uu____3220
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3220
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3219,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3221
                                                                    =
                                                                    let uu____3232
                                                                    =
                                                                    let uu____3241
                                                                    =
                                                                    let uu____3242
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3242
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3241,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3243
                                                                    =
                                                                    let uu____3254
                                                                    =
                                                                    let uu____3265
                                                                    =
                                                                    let uu____3274
                                                                    =
                                                                    let uu____3275
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3275
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3274,
                                                                    " ")  in
                                                                    let uu____3276
                                                                    =
                                                                    let uu____3287
                                                                    =
                                                                    let uu____3298
                                                                    =
                                                                    let uu____3309
                                                                    =
                                                                    let uu____3320
                                                                    =
                                                                    let uu____3331
                                                                    =
                                                                    let uu____3340
                                                                    =
                                                                    let uu____3341
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3341
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3340,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3342
                                                                    =
                                                                    let uu____3353
                                                                    =
                                                                    let uu____3362
                                                                    =
                                                                    let uu____3363
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3363
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3362,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3364
                                                                    =
                                                                    let uu____3375
                                                                    =
                                                                    let uu____3386
                                                                    =
                                                                    let uu____3395
                                                                    =
                                                                    let uu____3396
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3396
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3395,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3397
                                                                    =
                                                                    let uu____3408
                                                                    =
                                                                    let uu____3417
                                                                    =
                                                                    let uu____3418
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3418
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3417,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3419
                                                                    =
                                                                    let uu____3430
                                                                    =
                                                                    let uu____3439
                                                                    =
                                                                    let uu____3440
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3440
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3439,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3441
                                                                    =
                                                                    let uu____3452
                                                                    =
                                                                    let uu____3461
                                                                    =
                                                                    let uu____3462
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3462
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3461,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____3463
                                                                    =
                                                                    let uu____3474
                                                                    =
                                                                    let uu____3483
                                                                    =
                                                                    let uu____3484
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3484
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3483,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____3485
                                                                    =
                                                                    let uu____3496
                                                                    =
                                                                    let uu____3505
                                                                    =
                                                                    let uu____3506
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3506
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3505,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____3507
                                                                    =
                                                                    let uu____3518
                                                                    =
                                                                    let uu____3527
                                                                    =
                                                                    let uu____3528
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3528
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3527,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____3529
                                                                    =
                                                                    let uu____3540
                                                                    =
                                                                    let uu____3549
                                                                    =
                                                                    let uu____3550
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3550
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3549,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____3551
                                                                    =
                                                                    let uu____3562
                                                                    =
                                                                    let uu____3573
                                                                    =
                                                                    let uu____3582
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3583
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3582,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____3584
                                                                    =
                                                                    let uu____3595
                                                                    =
                                                                    let uu____3606
                                                                    =
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3638
                                                                    =
                                                                    let uu____3639
                                                                    =
                                                                    let uu____3646
                                                                    =
                                                                    let uu____3647
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3647
                                                                     in
                                                                    ((fun
                                                                    uu____3652
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3646)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3639
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____3638,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____3656
                                                                    =
                                                                    let uu____3668
                                                                    =
                                                                    let uu____3677
                                                                    =
                                                                    let uu____3678
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3678
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3677,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____3679
                                                                    =
                                                                    let uu____3690
                                                                    =
                                                                    let uu____3701
                                                                    =
                                                                    let uu____3710
                                                                    =
                                                                    let uu____3711
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3711
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3710,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____3712
                                                                    =
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3734
                                                                    =
                                                                    let uu____3745
                                                                    =
                                                                    let uu____3756
                                                                    =
                                                                    let uu____3767
                                                                    =
                                                                    let uu____3776
                                                                    =
                                                                    let uu____3777
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3777
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3776,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____3778
                                                                    =
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3799
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3798,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____3800
                                                                    =
                                                                    let uu____3811
                                                                    =
                                                                    let uu____3822
                                                                    =
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3833
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
                                                                    ((fun
                                                                    uu____3846
                                                                     ->
                                                                    (
                                                                    let uu____3848
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____3848);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3840)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3833
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____3832,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____3822]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3811
                                                                     in
                                                                    uu____3789
                                                                    ::
                                                                    uu____3800
                                                                     in
                                                                    uu____3767
                                                                    ::
                                                                    uu____3778
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3756
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3745
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3734
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3723
                                                                     in
                                                                    uu____3701
                                                                    ::
                                                                    uu____3712
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3690
                                                                     in
                                                                    uu____3668
                                                                    ::
                                                                    uu____3679
                                                                     in
                                                                    uu____3628
                                                                    ::
                                                                    uu____3656
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3617
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3606
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3595
                                                                     in
                                                                    uu____3573
                                                                    ::
                                                                    uu____3584
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3562
                                                                     in
                                                                    uu____3540
                                                                    ::
                                                                    uu____3551
                                                                     in
                                                                    uu____3518
                                                                    ::
                                                                    uu____3529
                                                                     in
                                                                    uu____3496
                                                                    ::
                                                                    uu____3507
                                                                     in
                                                                    uu____3474
                                                                    ::
                                                                    uu____3485
                                                                     in
                                                                    uu____3452
                                                                    ::
                                                                    uu____3463
                                                                     in
                                                                    uu____3430
                                                                    ::
                                                                    uu____3441
                                                                     in
                                                                    uu____3408
                                                                    ::
                                                                    uu____3419
                                                                     in
                                                                    uu____3386
                                                                    ::
                                                                    uu____3397
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3375
                                                                     in
                                                                    uu____3353
                                                                    ::
                                                                    uu____3364
                                                                     in
                                                                    uu____3331
                                                                    ::
                                                                    uu____3342
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3320
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3309
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3298
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3287
                                                                     in
                                                                    uu____3265
                                                                    ::
                                                                    uu____3276
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3254
                                                                     in
                                                                    uu____3232
                                                                    ::
                                                                    uu____3243
                                                                     in
                                                                    uu____3210
                                                                    ::
                                                                    uu____3221
                                                                     in
                                                                    uu____3188
                                                                    ::
                                                                    uu____3199
                                                                     in
                                                                    uu____3166
                                                                    ::
                                                                    uu____3177
                                                                     in
                                                                    uu____3144
                                                                    ::
                                                                    uu____3155
                                                                     in
                                                                    uu____3122
                                                                    ::
                                                                    uu____3133
                                                                     in
                                                                    uu____3100
                                                                    ::
                                                                    uu____3111
                                                                     in
                                                                    uu____3078
                                                                    ::
                                                                    uu____3089
                                                                     in
                                                                    uu____3056
                                                                    ::
                                                                    uu____3067
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3045
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3034
                                                                     in
                                                                    uu____3012
                                                                    ::
                                                                    uu____3023
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3001
                                                                     in
                                                                    uu____2979
                                                                    ::
                                                                    uu____2990
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2968
                                                                     in
                                                                    uu____2946
                                                                    ::
                                                                    uu____2957
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2935
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2924
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2913
                                                                     in
                                                                  uu____2891
                                                                    ::
                                                                    uu____2902
                                                                   in
                                                                uu____2869 ::
                                                                  uu____2880
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "load",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "module")),
                                                                "Load compiled module")
                                                                :: uu____2858
                                                               in
                                                            uu____2836 ::
                                                              uu____2847
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_ifuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                            :: uu____2825
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "initial_fuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of recursive functions to try initially (default 2)")
                                                          :: uu____2814
                                                         in
                                                      uu____2792 ::
                                                        uu____2803
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "include",
                                                      (ReverseAccumulated
                                                         (PathStr "path")),
                                                      "A directory in which to search for files included on the command line")
                                                      :: uu____2781
                                                     in
                                                  uu____2759 :: uu____2770
                                                   in
                                                uu____2737 :: uu____2748  in
                                              uu____2715 :: uu____2726  in
                                            (FStar_Getopt.noshort,
                                              "hint_file", (PathStr "path"),
                                              "Read/write hints to <path> (instead of module-specific hints files)")
                                              :: uu____2704
                                             in
                                          uu____2682 :: uu____2693  in
                                        (FStar_Getopt.noshort,
                                          "gen_native_tactics",
                                          (PathStr "[path]"),
                                          "Compile all user tactics used in the module in <path>")
                                          :: uu____2671
                                         in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____2660
                                       in
                                    uu____2638 :: uu____2649  in
                                  (FStar_Getopt.noshort, "extract_namespace",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "namespace name")))),
                                    "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                    :: uu____2627
                                   in
                                (FStar_Getopt.noshort, "extract_module",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "module_name")))),
                                  "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                  :: uu____2616
                                 in
                              (FStar_Getopt.noshort, "extract",
                                (Accumulated
                                   (SimpleStr
                                      "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                :: uu____2605
                               in
                            uu____2583 :: uu____2594  in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____2572
                           in
                        uu____2550 :: uu____2561  in
                      uu____2528 :: uu____2539  in
                    uu____2506 :: uu____2517  in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2495
                   in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2484
                 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2473
               in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2462
             in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2451
           in
        uu____2429 :: uu____2440  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2418
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2407

and (specs : Prims.unit -> FStar_Getopt.opt Prims.list) =
  fun uu____4562  ->
    let uu____4565 = specs_with_types ()  in
    FStar_List.map
      (fun uu____4590  ->
         match uu____4590 with
         | (short,long,typ,doc) ->
             let uu____4603 =
               let uu____4614 = arg_spec_of_opt_type long typ  in
               (short, long, uu____4614, doc)  in
             mk_spec uu____4603) uu____4565

let (settable : Prims.string -> Prims.bool) =
  fun uu___40_4621  ->
    match uu___40_4621 with
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
    | "timing" -> true
    | "trace_error" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "no_tactics" -> true
    | "tactic_raw_binders" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____4622 -> false
  
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
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4679  ->
          match uu____4679 with
          | (uu____4690,x,uu____4692,uu____4693) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4739  ->
          match uu____4739 with
          | (uu____4750,x,uu____4752,uu____4753) -> resettable x))
  
let (display_usage : Prims.unit -> Prims.unit) =
  fun uu____4760  ->
    let uu____4761 = specs ()  in display_usage_aux uu____4761
  
let (fstar_home : Prims.unit -> Prims.string) =
  fun uu____4776  ->
    let uu____4777 = get_fstar_home ()  in
    match uu____4777 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____4783 =
            let uu____4788 = mk_string x1  in ("fstar_home", uu____4788)  in
          set_option' uu____4783);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____4796 -> true
    | uu____4797 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____4804 -> uu____4804
  
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
          let uu____4848 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____4848
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4874  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4879 =
             let uu____4882 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____4882 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____4879)
       in
    let uu____4931 =
      let uu____4934 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4934
       in
    (res, uu____4931)
  
let (file_list : Prims.unit -> Prims.string Prims.list) =
  fun uu____4966  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____4999 = specs ()  in
       FStar_Getopt.parse_cmdline uu____4999 (fun x  -> ())  in
     (let uu____5005 =
        let uu____5010 =
          let uu____5011 = FStar_List.map mk_string old_verify_module  in
          List uu____5011  in
        ("verify_module", uu____5010)  in
      set_option' uu____5005);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5019 =
        let uu____5020 =
          let uu____5021 =
            let uu____5022 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5022  in
          (FStar_String.length f1) - uu____5021  in
        uu____5020 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5019  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5026 = get_lax ()  in
    if uu____5026
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5034 = module_name_of_file_name fn  in should_verify uu____5034
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5038 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5038
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5044 = should_verify m  in
    if uu____5044 then m <> "Prims" else false
  
let (include_path : Prims.unit -> Prims.string Prims.list) =
  fun uu____5050  ->
    let uu____5051 = get_no_default_includes ()  in
    if uu____5051
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5059 =
         let uu____5062 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5062
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5075 =
         let uu____5078 = get_include ()  in
         FStar_List.append uu____5078 ["."]  in
       FStar_List.append uu____5059 uu____5075)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5086 = FStar_Util.is_path_absolute filename  in
    if uu____5086
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5093 =
         let uu____5096 = include_path ()  in FStar_List.rev uu____5096  in
       FStar_Util.find_map uu____5093
         (fun p  ->
            let path = FStar_Util.join_paths p filename  in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : Prims.unit -> Prims.string) =
  fun uu____5108  ->
    let uu____5109 = get_prims ()  in
    match uu____5109 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5113 = find_file filename  in
        (match uu____5113 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5117 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5117)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : Prims.unit -> Prims.string) =
  fun uu____5121  ->
    let uu____5122 = prims ()  in FStar_Util.basename uu____5122
  
let (pervasives : Prims.unit -> Prims.string) =
  fun uu____5125  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5127 = find_file filename  in
    match uu____5127 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5131 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5131
  
let (pervasives_basename : Prims.unit -> Prims.string) =
  fun uu____5134  ->
    let uu____5135 = pervasives ()  in FStar_Util.basename uu____5135
  
let (pervasives_native_basename : Prims.unit -> Prims.string) =
  fun uu____5138  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5140 = find_file filename  in
    match uu____5140 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5144 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5144
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5148 = get_odir ()  in
    match uu____5148 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
  
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
             let uu____5203 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5203  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((FStar_Ident.path_of_text s1), true))
       in
    let uu____5211 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5211 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5279 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5279 (FStar_List.contains s)
  
let (admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____5286  -> get_admit_smt_queries () 
let (admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5291  -> get_admit_except () 
let (cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____5294  -> get_cache_checked_modules () 
let (codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5299  -> get_codegen () 
let (codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list) =
  fun uu____5306  ->
    let uu____5307 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____5307
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : Prims.unit -> Prims.bool) =
  fun uu____5322  -> let uu____5323 = get_debug ()  in uu____5323 <> [] 
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____5336 = get_debug ()  in
       FStar_All.pipe_right uu____5336 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5345  -> get_dep () 
let (detail_errors : Prims.unit -> Prims.bool) =
  fun uu____5348  -> get_detail_errors () 
let (detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____5351  -> get_detail_hint_replay () 
let (doc : Prims.unit -> Prims.bool) = fun uu____5354  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5358 = get_dump_module ()  in
    FStar_All.pipe_right uu____5358 (FStar_List.contains s)
  
let (eager_inference : Prims.unit -> Prims.bool) =
  fun uu____5365  -> get_eager_inference () 
let (expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5368  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____5372 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____5372
  
let (gen_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5402  -> get_gen_native_tactics () 
let (full_context_dependency : Prims.unit -> Prims.bool) =
  fun uu____5405  -> true 
let (hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____5408  -> get_hide_uvar_nums () 
let (hint_info : Prims.unit -> Prims.bool) =
  fun uu____5411  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5416  -> get_hint_file () 
let (ide : Prims.unit -> Prims.bool) = fun uu____5419  -> get_ide () 
let (indent : Prims.unit -> Prims.bool) = fun uu____5422  -> get_indent () 
let (initial_fuel : Prims.unit -> Prims.int) =
  fun uu____5425  ->
    let uu____5426 = get_initial_fuel ()  in
    let uu____5427 = get_max_fuel ()  in Prims.min uu____5426 uu____5427
  
let (initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____5430  ->
    let uu____5431 = get_initial_ifuel ()  in
    let uu____5432 = get_max_ifuel ()  in Prims.min uu____5431 uu____5432
  
let (interactive : Prims.unit -> Prims.bool) =
  fun uu____5435  -> (get_in ()) || (get_ide ()) 
let (lax : Prims.unit -> Prims.bool) = fun uu____5438  -> get_lax () 
let (load : Prims.unit -> Prims.string Prims.list) =
  fun uu____5443  -> get_load () 
let (legacy_interactive : Prims.unit -> Prims.bool) =
  fun uu____5446  -> get_in () 
let (log_queries : Prims.unit -> Prims.bool) =
  fun uu____5449  -> get_log_queries () 
let (log_types : Prims.unit -> Prims.bool) =
  fun uu____5452  -> get_log_types () 
let (max_fuel : Prims.unit -> Prims.int) = fun uu____5455  -> get_max_fuel () 
let (max_ifuel : Prims.unit -> Prims.int) =
  fun uu____5458  -> get_max_ifuel () 
let (min_fuel : Prims.unit -> Prims.int) = fun uu____5461  -> get_min_fuel () 
let (ml_ish : Prims.unit -> Prims.bool) = fun uu____5464  -> get_MLish () 
let (set_ml_ish : Prims.unit -> Prims.unit) =
  fun uu____5467  -> set_option "MLish" (Bool true) 
let (n_cores : Prims.unit -> Prims.int) = fun uu____5470  -> get_n_cores () 
let (no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____5473  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____5478 = get_no_extract ()  in
    FStar_All.pipe_right uu____5478
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (no_location_info : Prims.unit -> Prims.bool) =
  fun uu____5487  -> get_no_location_info () 
let (output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____5492  -> get_odir () 
let (ugly : Prims.unit -> Prims.bool) = fun uu____5495  -> get_ugly () 
let (print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____5498  -> get_print_bound_var_types () 
let (print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____5501  -> get_print_effect_args () 
let (print_implicits : Prims.unit -> Prims.bool) =
  fun uu____5504  -> get_print_implicits () 
let (print_real_names : Prims.unit -> Prims.bool) =
  fun uu____5507  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : Prims.unit -> Prims.bool) =
  fun uu____5510  -> get_print_universes () 
let (print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____5513  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : Prims.unit -> Prims.bool) =
  fun uu____5516  -> get_query_stats () 
let (record_hints : Prims.unit -> Prims.bool) =
  fun uu____5519  -> get_record_hints () 
let (reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5524  -> get_reuse_hint_for () 
let (silent : Prims.unit -> Prims.bool) = fun uu____5527  -> get_silent () 
let (smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____5530  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5533  ->
    let uu____5534 = get_smtencoding_nl_arith_repr ()  in
    uu____5534 = "native"
  
let (smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool) =
  fun uu____5537  ->
    let uu____5538 = get_smtencoding_nl_arith_repr ()  in
    uu____5538 = "wrapped"
  
let (smtencoding_nl_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5541  ->
    let uu____5542 = get_smtencoding_nl_arith_repr ()  in
    uu____5542 = "boxwrap"
  
let (smtencoding_l_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5545  ->
    let uu____5546 = get_smtencoding_l_arith_repr ()  in
    uu____5546 = "native"
  
let (smtencoding_l_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5549  ->
    let uu____5550 = get_smtencoding_l_arith_repr ()  in
    uu____5550 = "boxwrap"
  
let (tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____5553  -> get_tactic_raw_binders () 
let (tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____5556  -> get_tactic_trace () 
let (tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____5559  -> get_tactic_trace_d () 
let (timing : Prims.unit -> Prims.bool) = fun uu____5562  -> get_timing () 
let (trace_error : Prims.unit -> Prims.bool) =
  fun uu____5565  -> get_trace_error () 
let (unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____5568  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____5571  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____5574  -> get_use_eq_at_higher_order () 
let (use_hints : Prims.unit -> Prims.bool) =
  fun uu____5577  -> get_use_hints () 
let (use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____5580  -> get_use_hint_hashes () 
let (use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5585  -> get_use_native_tactics () 
let (use_tactics : Prims.unit -> Prims.bool) =
  fun uu____5588  -> get_use_tactics () 
let (using_facts_from :
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____5597  ->
    let uu____5598 = get_using_facts_from ()  in
    match uu____5598 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : Prims.unit -> Prims.bool) =
  fun uu____5632  ->
    let uu____5633 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____5633
  
let (vcgen_decorate_with_type : Prims.unit -> Prims.bool) =
  fun uu____5638  ->
    let uu____5639 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____5639 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5642 -> false
  
let (warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____5647  -> get_warn_default_effects () 
let (z3_exe : Prims.unit -> Prims.string) =
  fun uu____5650  ->
    let uu____5651 = get_smt ()  in
    match uu____5651 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____5659  -> get_z3cliopt () 
let (z3_refresh : Prims.unit -> Prims.bool) =
  fun uu____5662  -> get_z3refresh () 
let (z3_rlimit : Prims.unit -> Prims.int) =
  fun uu____5665  -> get_z3rlimit () 
let (z3_rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____5668  -> get_z3rlimit_factor () 
let (z3_seed : Prims.unit -> Prims.int) = fun uu____5671  -> get_z3seed () 
let (use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____5674  -> get_use_two_phase_tc () 
let (no_positivity : Prims.unit -> Prims.bool) =
  fun uu____5677  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____5680  -> get_ml_no_eta_expand_coertions () 
let (warn_error : Prims.unit -> Prims.string) =
  fun uu____5683  -> get_warn_error () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____5688 = get_extract ()  in
    match uu____5688 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5699 =
            let uu____5712 = get_no_extract ()  in
            let uu____5715 = get_extract_namespace ()  in
            let uu____5718 = get_extract_module ()  in
            (uu____5712, uu____5715, uu____5718)  in
          match uu____5699 with
          | ([],[],[]) -> ()
          | uu____5733 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____5777,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____5796 -> false  in
          let uu____5805 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____5839  ->
                    match uu____5839 with
                    | (path,uu____5847) -> matches_path m_components path))
             in
          match uu____5805 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____5858,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____5876 = get_extract_namespace ()  in
          match uu____5876 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____5890 = get_extract_module ()  in
          match uu____5890 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____5902 = no_extract m1  in Prims.op_Negation uu____5902) &&
          (let uu____5904 =
             let uu____5913 = get_extract_namespace ()  in
             let uu____5916 = get_extract_module ()  in
             (uu____5913, uu____5916)  in
           (match uu____5904 with
            | ([],[]) -> true
            | uu____5927 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (codegen_fsharp : Prims.unit -> Prims.bool) =
  fun uu____5938  ->
    let uu____5939 = codegen ()  in
    uu____5939 = (FStar_Pervasives_Native.Some "FSharp")
  