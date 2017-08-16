open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let uu___is_Low : debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____9 -> false 
let uu___is_Medium : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____14 -> false
  
let uu___is_High : debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____19 -> false 
let uu___is_Extreme : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____24 -> false
  
let uu___is_Other : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____30 -> false
  
let __proj__Other__item___0 : debug_level_t -> Prims.string =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let uu___is_Bool : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____66 -> false
  
let __proj__Bool__item___0 : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let uu___is_String : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____80 -> false
  
let __proj__String__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0 
let uu___is_Path : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____94 -> false
  
let __proj__Path__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0 
let uu___is_Int : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____108 -> false
  
let __proj__Int__item___0 : option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0 
let uu___is_List : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____124 -> false
  
let __proj__List__item___0 : option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0 
let uu___is_Unset : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____143 -> false
  
let mk_bool : Prims.bool -> option_val = fun _0_28  -> Bool _0_28 
let mk_string : Prims.string -> option_val = fun _0_29  -> String _0_29 
let mk_path : Prims.string -> option_val = fun _0_30  -> Path _0_30 
let mk_int : Prims.int -> option_val = fun _0_31  -> Int _0_31 
let mk_list : option_val Prims.list -> option_val = fun _0_32  -> List _0_32 
type options =
  | Set 
  | Reset 
  | Restore 
let uu___is_Set : options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____165 -> false 
let uu___is_Reset : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____170 -> false
  
let uu___is_Restore : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____175 -> false
  
type solver =
  | Z3 
  | CVC4 
let uu___is_Z3 : solver -> Prims.bool =
  fun projectee  -> match projectee with | Z3  -> true | uu____180 -> false 
let uu___is_CVC4 : solver -> Prims.bool =
  fun projectee  -> match projectee with | CVC4  -> true | uu____185 -> false 
let __unit_tests__ : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let __unit_tests : Prims.unit -> Prims.bool =
  fun uu____198  -> FStar_ST.op_Bang __unit_tests__ 
let __set_unit_tests : Prims.unit -> Prims.unit =
  fun uu____212  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let __clear_unit_tests : Prims.unit -> Prims.unit =
  fun uu____226  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let as_bool : option_val -> Prims.bool =
  fun uu___49_240  ->
    match uu___49_240 with
    | Bool b -> b
    | uu____242 -> failwith "Impos: expected Bool"
  
let as_int : option_val -> Prims.int =
  fun uu___50_246  ->
    match uu___50_246 with
    | Int b -> b
    | uu____248 -> failwith "Impos: expected Int"
  
let as_string : option_val -> Prims.string =
  fun uu___51_252  ->
    match uu___51_252 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____255 -> failwith "Impos: expected String"
  
let as_list :
  'Auu____262 .
    (option_val -> 'Auu____262) -> option_val -> 'Auu____262 Prims.list
  =
  fun as_t  ->
    fun uu___52_275  ->
      match uu___52_275 with
      | List ts -> FStar_All.pipe_right ts (FStar_List.map as_t)
      | uu____285 -> failwith "Impos: expected List"
  
let as_option :
  'Auu____294 .
    (option_val -> 'Auu____294) ->
      option_val -> 'Auu____294 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___53_307  ->
      match uu___53_307 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____311 = as_t v1  in FStar_Pervasives_Native.Some uu____311
  
type optionstate = option_val FStar_Util.smap
let fstar_options : optionstate Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let peek : Prims.unit -> optionstate =
  fun uu____330  ->
    let uu____331 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____331
  
let pop : Prims.unit -> Prims.unit =
  fun uu____355  ->
    let uu____356 = FStar_ST.op_Bang fstar_options  in
    match uu____356 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____377::[] -> failwith "TOO MANY POPS!"
    | uu____378::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let push : Prims.unit -> Prims.unit =
  fun uu____403  ->
    let uu____404 =
      let uu____407 =
        let uu____410 = peek ()  in FStar_Util.smap_copy uu____410  in
      let uu____413 = FStar_ST.op_Bang fstar_options  in uu____407 ::
        uu____413
       in
    FStar_ST.op_Colon_Equals fstar_options uu____404
  
let set : optionstate -> Prims.unit =
  fun o  ->
    let uu____460 = FStar_ST.op_Bang fstar_options  in
    match uu____460 with
    | [] -> failwith "set on empty option stack"
    | uu____481::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let set_option : Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____511 = peek ()  in FStar_Util.smap_add uu____511 k v1
  
let set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____521  -> match uu____521 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let light_off_files : Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let add_light_off_file : Prims.string -> Prims.unit =
  fun filename  ->
    let uu____562 =
      let uu____565 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____565
       in
    FStar_ST.op_Colon_Equals light_off_files uu____562
  
let defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
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
  ("explicit_deps", (Bool false));
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("fstar_home", Unset);
  ("full_context_dependency", (Bool true));
  ("hide_genident_nums", (Bool false));
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
  ("show_signatures", (List []));
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("smt_solver", (String "z3"));
  ("split_cases", (Int (Prims.parse_int "0")));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("no_tactics", (Bool false));
  ("using_facts_from", Unset);
  ("verify", (Bool true));
  ("verify_all", (Bool false));
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false))] 
let init : Prims.unit -> Prims.unit =
  fun uu____957  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let clear : Prims.unit -> Prims.unit =
  fun uu____973  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let _run : Prims.unit = clear () 
let get_option : Prims.string -> option_val =
  fun s  ->
    let uu____1023 =
      let uu____1026 = peek ()  in FStar_Util.smap_try_find uu____1026 s  in
    match uu____1023 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1036 . Prims.string -> (option_val -> 'Auu____1036) -> 'Auu____1036
  = fun s  -> fun c  -> c (get_option s) 
let get_admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____1053  -> lookup_opt "admit_smt_queries" as_bool 
let get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1059  -> lookup_opt "admit_except" (as_option as_string) 
let get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1067  -> lookup_opt "codegen" (as_option as_string) 
let get_codegen_lib : Prims.unit -> Prims.string Prims.list =
  fun uu____1075  -> lookup_opt "codegen-lib" (as_list as_string) 
let get_debug : Prims.unit -> Prims.string Prims.list =
  fun uu____1083  -> lookup_opt "debug" (as_list as_string) 
let get_debug_level : Prims.unit -> Prims.string Prims.list =
  fun uu____1091  -> lookup_opt "debug_level" (as_list as_string) 
let get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1099  -> lookup_opt "dep" (as_option as_string) 
let get_detail_errors : Prims.unit -> Prims.bool =
  fun uu____1105  -> lookup_opt "detail_errors" as_bool 
let get_detail_hint_replay : Prims.unit -> Prims.bool =
  fun uu____1109  -> lookup_opt "detail_hint_replay" as_bool 
let get_doc : Prims.unit -> Prims.bool =
  fun uu____1113  -> lookup_opt "doc" as_bool 
let get_dump_module : Prims.unit -> Prims.string Prims.list =
  fun uu____1119  -> lookup_opt "dump_module" (as_list as_string) 
let get_eager_inference : Prims.unit -> Prims.bool =
  fun uu____1125  -> lookup_opt "eager_inference" as_bool 
let get_explicit_deps : Prims.unit -> Prims.bool =
  fun uu____1129  -> lookup_opt "explicit_deps" as_bool 
let get_extract_all : Prims.unit -> Prims.bool =
  fun uu____1133  -> lookup_opt "extract_all" as_bool 
let get_extract_module : Prims.unit -> Prims.string Prims.list =
  fun uu____1139  -> lookup_opt "extract_module" (as_list as_string) 
let get_extract_namespace : Prims.unit -> Prims.string Prims.list =
  fun uu____1147  -> lookup_opt "extract_namespace" (as_list as_string) 
let get_fs_typ_app : Prims.unit -> Prims.bool =
  fun uu____1153  -> lookup_opt "fs_typ_app" as_bool 
let get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1159  -> lookup_opt "fstar_home" (as_option as_string) 
let get_hide_genident_nums : Prims.unit -> Prims.bool =
  fun uu____1165  -> lookup_opt "hide_genident_nums" as_bool 
let get_hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____1169  -> lookup_opt "hide_uvar_nums" as_bool 
let get_hint_info : Prims.unit -> Prims.bool =
  fun uu____1173  -> lookup_opt "hint_info" as_bool 
let get_hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1179  -> lookup_opt "hint_file" (as_option as_string) 
let get_in : Prims.unit -> Prims.bool =
  fun uu____1185  -> lookup_opt "in" as_bool 
let get_ide : Prims.unit -> Prims.bool =
  fun uu____1189  -> lookup_opt "ide" as_bool 
let get_include : Prims.unit -> Prims.string Prims.list =
  fun uu____1195  -> lookup_opt "include" (as_list as_string) 
let get_indent : Prims.unit -> Prims.bool =
  fun uu____1201  -> lookup_opt "indent" as_bool 
let get_initial_fuel : Prims.unit -> Prims.int =
  fun uu____1205  -> lookup_opt "initial_fuel" as_int 
let get_initial_ifuel : Prims.unit -> Prims.int =
  fun uu____1209  -> lookup_opt "initial_ifuel" as_int 
let get_lax : Prims.unit -> Prims.bool =
  fun uu____1213  -> lookup_opt "lax" as_bool 
let get_load : Prims.unit -> Prims.string Prims.list =
  fun uu____1219  -> lookup_opt "load" (as_list as_string) 
let get_log_queries : Prims.unit -> Prims.bool =
  fun uu____1225  -> lookup_opt "log_queries" as_bool 
let get_log_types : Prims.unit -> Prims.bool =
  fun uu____1229  -> lookup_opt "log_types" as_bool 
let get_max_fuel : Prims.unit -> Prims.int =
  fun uu____1233  -> lookup_opt "max_fuel" as_int 
let get_max_ifuel : Prims.unit -> Prims.int =
  fun uu____1237  -> lookup_opt "max_ifuel" as_int 
let get_min_fuel : Prims.unit -> Prims.int =
  fun uu____1241  -> lookup_opt "min_fuel" as_int 
let get_MLish : Prims.unit -> Prims.bool =
  fun uu____1245  -> lookup_opt "MLish" as_bool 
let get_n_cores : Prims.unit -> Prims.int =
  fun uu____1249  -> lookup_opt "n_cores" as_int 
let get_no_default_includes : Prims.unit -> Prims.bool =
  fun uu____1253  -> lookup_opt "no_default_includes" as_bool 
let get_no_extract : Prims.unit -> Prims.string Prims.list =
  fun uu____1259  -> lookup_opt "no_extract" (as_list as_string) 
let get_no_location_info : Prims.unit -> Prims.bool =
  fun uu____1265  -> lookup_opt "no_location_info" as_bool 
let get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1271  -> lookup_opt "odir" (as_option as_string) 
let get_ugly : Prims.unit -> Prims.bool =
  fun uu____1277  -> lookup_opt "ugly" as_bool 
let get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1283  -> lookup_opt "prims" (as_option as_string) 
let get_print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____1289  -> lookup_opt "print_bound_var_types" as_bool 
let get_print_effect_args : Prims.unit -> Prims.bool =
  fun uu____1293  -> lookup_opt "print_effect_args" as_bool 
let get_print_full_names : Prims.unit -> Prims.bool =
  fun uu____1297  -> lookup_opt "print_full_names" as_bool 
let get_print_implicits : Prims.unit -> Prims.bool =
  fun uu____1301  -> lookup_opt "print_implicits" as_bool 
let get_print_universes : Prims.unit -> Prims.bool =
  fun uu____1305  -> lookup_opt "print_universes" as_bool 
let get_print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____1309  -> lookup_opt "print_z3_statistics" as_bool 
let get_prn : Prims.unit -> Prims.bool =
  fun uu____1313  -> lookup_opt "prn" as_bool 
let get_query_stats : Prims.unit -> Prims.bool =
  fun uu____1317  -> lookup_opt "query_stats" as_bool 
let get_record_hints : Prims.unit -> Prims.bool =
  fun uu____1321  -> lookup_opt "record_hints" as_bool 
let get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1327  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let get_show_signatures : Prims.unit -> Prims.string Prims.list =
  fun uu____1335  -> lookup_opt "show_signatures" (as_list as_string) 
let get_silent : Prims.unit -> Prims.bool =
  fun uu____1341  -> lookup_opt "silent" as_bool 
let get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1347  -> lookup_opt "smt" (as_option as_string) 
let get_smtencoding_elim_box : Prims.unit -> Prims.bool =
  fun uu____1353  -> lookup_opt "smtencoding.elim_box" as_bool 
let get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string =
  fun uu____1357  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let get_smtencoding_l_arith_repr : Prims.unit -> Prims.string =
  fun uu____1361  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let get_smtsolver : Prims.unit -> Prims.string =
  fun uu____1365  -> lookup_opt "smt_solver" as_string 
let get_split_cases : Prims.unit -> Prims.int =
  fun uu____1369  -> lookup_opt "split_cases" as_int 
let get_timing : Prims.unit -> Prims.bool =
  fun uu____1373  -> lookup_opt "timing" as_bool 
let get_trace_error : Prims.unit -> Prims.bool =
  fun uu____1377  -> lookup_opt "trace_error" as_bool 
let get_unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____1381  -> lookup_opt "unthrottle_inductives" as_bool 
let get_use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____1385  -> lookup_opt "use_eq_at_higher_order" as_bool 
let get_use_hints : Prims.unit -> Prims.bool =
  fun uu____1389  -> lookup_opt "use_hints" as_bool 
let get_use_tactics : Prims.unit -> Prims.bool =
  fun uu____1393  ->
    let uu____1394 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1394
  
let get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1402  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let get_verify_all : Prims.unit -> Prims.bool =
  fun uu____1412  -> lookup_opt "verify_all" as_bool 
let get_verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____1418  -> lookup_opt "verify_module" (as_list as_string) 
let get___temp_no_proj : Prims.unit -> Prims.string Prims.list =
  fun uu____1426  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let get_version : Prims.unit -> Prims.bool =
  fun uu____1432  -> lookup_opt "version" as_bool 
let get_warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____1436  -> lookup_opt "warn_default_effects" as_bool 
let get_z3cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____1442  -> lookup_opt "z3cliopt" (as_list as_string) 
let get_z3refresh : Prims.unit -> Prims.bool =
  fun uu____1448  -> lookup_opt "z3refresh" as_bool 
let get_z3rlimit : Prims.unit -> Prims.int =
  fun uu____1452  -> lookup_opt "z3rlimit" as_int 
let get_z3rlimit_factor : Prims.unit -> Prims.int =
  fun uu____1456  -> lookup_opt "z3rlimit_factor" as_int 
let get_z3seed : Prims.unit -> Prims.int =
  fun uu____1460  -> lookup_opt "z3seed" as_int 
let get_no_positivity : Prims.unit -> Prims.bool =
  fun uu____1464  -> lookup_opt "__no_positivity" as_bool 
let get_ml_no_eta_expand_coertions : Prims.unit -> Prims.bool =
  fun uu____1468  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let dlevel : Prims.string -> debug_level_t =
  fun uu___54_1472  ->
    match uu___54_1472 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1482 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let debug_level_geq : debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1487 = get_debug_level ()  in
    FStar_All.pipe_right uu____1487
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let universe_include_path_base_dirs : Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"] 
let _version : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _platform : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _compiler : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _date : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _commit : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let display_version : Prims.unit -> Prims.unit =
  fun uu____1579  ->
    let uu____1580 =
      let uu____1581 = FStar_ST.op_Bang _version  in
      let uu____1592 = FStar_ST.op_Bang _platform  in
      let uu____1603 = FStar_ST.op_Bang _compiler  in
      let uu____1614 = FStar_ST.op_Bang _date  in
      let uu____1625 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1581
        uu____1592 uu____1603 uu____1614 uu____1625
       in
    FStar_Util.print_string uu____1580
  
let display_usage_aux :
  'Auu____1642 'Auu____1643 .
    ('Auu____1643,Prims.string,'Auu____1642 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1690  ->
         match uu____1690 with
         | (uu____1701,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1712 =
                      let uu____1713 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____1713  in
                    FStar_Util.print_string uu____1712
                  else
                    (let uu____1715 =
                       let uu____1716 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____1716 doc  in
                     FStar_Util.print_string uu____1715)
              | FStar_Getopt.OneArg (uu____1717,argname) ->
                  if doc = ""
                  then
                    let uu____1723 =
                      let uu____1724 = FStar_Util.colorize_bold flag  in
                      let uu____1725 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____1724 uu____1725
                       in
                    FStar_Util.print_string uu____1723
                  else
                    (let uu____1727 =
                       let uu____1728 = FStar_Util.colorize_bold flag  in
                       let uu____1729 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1728
                         uu____1729 doc
                        in
                     FStar_Util.print_string uu____1727))) specs
  
let mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1754 = o  in
    match uu____1754 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1784 =
                let uu____1785 = let uu____1790 = f ()  in (name, uu____1790)
                   in
                set_option' uu____1785  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x =
                let uu____1801 = let uu____1806 = f x  in (name, uu____1806)
                   in
                set_option' uu____1801  in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let cons_extract_module : Prims.string -> option_val =
  fun s  ->
    let uu____1815 =
      let uu____1818 =
        let uu____1821 = get_extract_module ()  in (FStar_String.lowercase s)
          :: uu____1821
         in
      FStar_All.pipe_right uu____1818
        (FStar_List.map (fun _0_33  -> String _0_33))
       in
    List uu____1815
  
let cons_extract_namespace : Prims.string -> option_val =
  fun s  ->
    let uu____1832 =
      let uu____1835 =
        let uu____1838 = get_extract_namespace ()  in
        (FStar_String.lowercase s) :: uu____1838  in
      FStar_All.pipe_right uu____1835
        (FStar_List.map (fun _0_34  -> String _0_34))
       in
    List uu____1832
  
let add_extract_module : Prims.string -> Prims.unit =
  fun s  ->
    let uu____1849 = cons_extract_module s  in
    set_option "extract_module" uu____1849
  
let add_extract_namespace : Prims.string -> Prims.unit =
  fun s  ->
    let uu____1854 = cons_extract_namespace s  in
    set_option "extract_namespace" uu____1854
  
let cons_verify_module : Prims.string -> option_val =
  fun s  ->
    let uu____1859 =
      let uu____1862 =
        let uu____1865 = get_verify_module ()  in (FStar_String.lowercase s)
          :: uu____1865
         in
      FStar_All.pipe_right uu____1862
        (FStar_List.map (fun _0_35  -> String _0_35))
       in
    List uu____1859
  
let cons_using_facts_from : Prims.string -> option_val =
  fun s  ->
    set_option "z3refresh" (Bool true);
    (let uu____1877 = get_using_facts_from ()  in
     match uu____1877 with
     | FStar_Pervasives_Native.None  -> List [String s]
     | FStar_Pervasives_Native.Some l ->
         let uu____1889 =
           FStar_List.map (fun _0_36  -> String _0_36) (s :: l)  in
         List uu____1889)
  
let add_verify_module : Prims.string -> Prims.unit =
  fun s  ->
    let uu____1896 = cons_verify_module s  in
    set_option "verify_module" uu____1896
  
let rec specs : Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____1911  ->
    let specs1 =
      [(FStar_Getopt.noshort, "admit_smt_queries",
         (FStar_Getopt.OneArg
            (((fun s  ->
                 if s = "true"
                 then mk_bool true
                 else
                   if s = "false"
                   then mk_bool false
                   else failwith "Invalid argument to --admit_smt_queries")),
              "[true|false]")),
         "Admit SMT queries, unsafe! (default 'false')");
      (FStar_Getopt.noshort, "admit_except",
        (FStar_Getopt.OneArg (mk_string, "[id]")),
        "Admit all verification conditions, except those with query label <id> (eg, --admit_except '(FStar.Fin.pigeonhole, 1)'");
      (FStar_Getopt.noshort, "codegen",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1976 = parse_codegen s  in mk_string uu____1976)),
             "[OCaml|FSharp|Kremlin]")), "Generate code for execution");
      (FStar_Getopt.noshort, "codegen-lib",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1994 =
                  let uu____1997 =
                    let uu____2000 = get_codegen_lib ()  in s :: uu____2000
                     in
                  FStar_All.pipe_right uu____1997 (FStar_List.map mk_string)
                   in
                List uu____1994)), "[namespace]")),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
      (FStar_Getopt.noshort, "debug",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2024 =
                  let uu____2027 =
                    let uu____2030 = get_debug ()  in x :: uu____2030  in
                  FStar_All.pipe_right uu____2027 (FStar_List.map mk_string)
                   in
                List uu____2024)), "[module name]")),
        "Print lots of debugging information while checking module");
      (FStar_Getopt.noshort, "debug_level",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2054 =
                  let uu____2057 =
                    let uu____2060 = get_debug_level ()  in x :: uu____2060
                     in
                  FStar_All.pipe_right uu____2057 (FStar_List.map mk_string)
                   in
                List uu____2054)), "[Low|Medium|High|Extreme|...]")),
        "Control the verbosity of debugging info");
      (FStar_Getopt.noshort, "dep",
        (FStar_Getopt.OneArg
           (((fun x  ->
                if (x = "make") || (x = "graph")
                then mk_string x
                else failwith "invalid argument to 'dep'")), "[make|graph]")),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");
      (FStar_Getopt.noshort, "detail_errors",
        (FStar_Getopt.ZeroArgs ((fun uu____2097  -> mk_bool true))),
        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "detail_hint_replay",
        (FStar_Getopt.ZeroArgs ((fun uu____2111  -> mk_bool true))),
        "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "doc",
        (FStar_Getopt.ZeroArgs ((fun uu____2125  -> mk_bool true))),
        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");
      (FStar_Getopt.noshort, "dump_module",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2143 =
                  let uu____2146 =
                    let uu____2149 = get_dump_module ()  in x :: uu____2149
                     in
                  FStar_All.pipe_right uu____2146 (FStar_List.map mk_string)
                   in
                FStar_All.pipe_right uu____2143 mk_list)), "[module name]")),
        "");
      (FStar_Getopt.noshort, "eager_inference",
        (FStar_Getopt.ZeroArgs ((fun uu____2171  -> mk_bool true))),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
      (FStar_Getopt.noshort, "explicit_deps",
        (FStar_Getopt.ZeroArgs ((fun uu____2185  -> mk_bool true))),
        "Do not find dependencies automatically, the user provides them on the command-line");
      (FStar_Getopt.noshort, "extract_all",
        (FStar_Getopt.ZeroArgs ((fun uu____2199  -> mk_bool true))),
        "Discover the complete dependency graph and do not stop at interface boundaries");
      (FStar_Getopt.noshort, "extract_module",
        (FStar_Getopt.OneArg (cons_extract_module, "[module name]")),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");
      (FStar_Getopt.noshort, "extract_namespace",
        (FStar_Getopt.OneArg (cons_extract_namespace, "[namespace name]")),
        "Only extract modules in the specified namespace");
      (FStar_Getopt.noshort, "fstar_home",
        (FStar_Getopt.OneArg (mk_path, "[dir]")),
        "Set the FSTAR_HOME variable to [dir]");
      (FStar_Getopt.noshort, "hide_genident_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____2255  -> mk_bool true))),
        "Don't print generated identifier numbers");
      (FStar_Getopt.noshort, "hide_uvar_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____2269  -> mk_bool true))),
        "Don't print unification variable numbers");
      (FStar_Getopt.noshort, "hint_file",
        (FStar_Getopt.OneArg (mk_path, "[path]")),
        "Read/write hints to <path> (instead of module-specific hints files)");
      (FStar_Getopt.noshort, "hint_info",
        (FStar_Getopt.ZeroArgs ((fun uu____2297  -> mk_bool true))),
        "Print information regarding hints (deprecated; use --query_stats instead)");
      (FStar_Getopt.noshort, "in",
        (FStar_Getopt.ZeroArgs ((fun uu____2311  -> mk_bool true))),
        "Legacy interactive mode; reads input from stdin");
      (FStar_Getopt.noshort, "ide",
        (FStar_Getopt.ZeroArgs ((fun uu____2325  -> mk_bool true))),
        "JSON-based interactive mode for IDEs");
      (FStar_Getopt.noshort, "include",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____2343 =
                  let uu____2346 =
                    let uu____2349 = get_include ()  in
                    FStar_List.map mk_string uu____2349  in
                  let uu____2352 =
                    let uu____2355 = mk_path s  in [uu____2355]  in
                  FStar_List.append uu____2346 uu____2352  in
                mk_list uu____2343)), "[path]")),
        "A directory in which to search for files included on the command line");
      (FStar_Getopt.noshort, "indent",
        (FStar_Getopt.ZeroArgs ((fun uu____2369  -> mk_bool true))),
        "Parses and outputs the files on the command line");
      (FStar_Getopt.noshort, "initial_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2387 = FStar_Util.int_of_string x  in
                mk_int uu____2387)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try initially (default 2)");
      (FStar_Getopt.noshort, "initial_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2405 = FStar_Util.int_of_string x  in
                mk_int uu____2405)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at first (default 1)");
      (FStar_Getopt.noshort, "inline_arith",
        (FStar_Getopt.ZeroArgs ((fun uu____2419  -> mk_bool true))),
        "Inline definitions of arithmetic functions in the SMT encoding");
      (FStar_Getopt.noshort, "lax",
        (FStar_Getopt.ZeroArgs ((fun uu____2433  -> mk_bool true))),
        "Run the lax-type checker only (admit all verification conditions)");
      (FStar_Getopt.noshort, "load",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____2451 =
                  let uu____2454 =
                    let uu____2457 = get_load ()  in
                    FStar_List.map mk_string uu____2457  in
                  let uu____2460 =
                    let uu____2463 = mk_path s  in [uu____2463]  in
                  FStar_List.append uu____2454 uu____2460  in
                mk_list uu____2451)), "[module]")), "Load compiled module");
      (FStar_Getopt.noshort, "log_types",
        (FStar_Getopt.ZeroArgs ((fun uu____2477  -> mk_bool true))),
        "Print types computed for data/val/let-bindings");
      (FStar_Getopt.noshort, "log_queries",
        (FStar_Getopt.ZeroArgs ((fun uu____2491  -> mk_bool true))),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");
      (FStar_Getopt.noshort, "max_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2509 = FStar_Util.int_of_string x  in
                mk_int uu____2509)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try at most (default 8)");
      (FStar_Getopt.noshort, "max_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2527 = FStar_Util.int_of_string x  in
                mk_int uu____2527)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at most (default 2)");
      (FStar_Getopt.noshort, "min_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2545 = FStar_Util.int_of_string x  in
                mk_int uu____2545)), "[non-negative integer]")),
        "Minimum number of unrolling of recursive functions to try (default 1)");
      (FStar_Getopt.noshort, "MLish",
        (FStar_Getopt.ZeroArgs ((fun uu____2559  -> mk_bool true))),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
      (FStar_Getopt.noshort, "n_cores",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2577 = FStar_Util.int_of_string x  in
                mk_int uu____2577)), "[positive integer]")),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");
      (FStar_Getopt.noshort, "no_default_includes",
        (FStar_Getopt.ZeroArgs ((fun uu____2591  -> mk_bool true))),
        "Ignore the default module search paths");
      (FStar_Getopt.noshort, "no_extract",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2609 =
                  let uu____2612 =
                    let uu____2615 = get_no_extract ()  in x :: uu____2615
                     in
                  FStar_All.pipe_right uu____2612 (FStar_List.map mk_string)
                   in
                mk_list uu____2609)), "[module name]")),
        "Do not extract code from this module");
      (FStar_Getopt.noshort, "no_location_info",
        (FStar_Getopt.ZeroArgs ((fun uu____2635  -> mk_bool true))),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
      (FStar_Getopt.noshort, "odir",
        (FStar_Getopt.OneArg
           (((fun p  ->
                let uu____2653 = validate_dir p  in mk_path uu____2653)),
             "[dir]")), "Place output in directory [dir]");
      (FStar_Getopt.noshort, "prims",
        (FStar_Getopt.OneArg (mk_string, "file")), "");
      (FStar_Getopt.noshort, "print_bound_var_types",
        (FStar_Getopt.ZeroArgs ((fun uu____2681  -> mk_bool true))),
        "Print the types of bound variables");
      (FStar_Getopt.noshort, "print_effect_args",
        (FStar_Getopt.ZeroArgs ((fun uu____2695  -> mk_bool true))),
        "Print inferred predicate transformers for all computation types");
      (FStar_Getopt.noshort, "print_full_names",
        (FStar_Getopt.ZeroArgs ((fun uu____2709  -> mk_bool true))),
        "Print full names of variables");
      (FStar_Getopt.noshort, "print_implicits",
        (FStar_Getopt.ZeroArgs ((fun uu____2723  -> mk_bool true))),
        "Print implicit arguments");
      (FStar_Getopt.noshort, "print_universes",
        (FStar_Getopt.ZeroArgs ((fun uu____2737  -> mk_bool true))),
        "Print universes");
      (FStar_Getopt.noshort, "print_z3_statistics",
        (FStar_Getopt.ZeroArgs ((fun uu____2751  -> mk_bool true))),
        "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)");
      (FStar_Getopt.noshort, "prn",
        (FStar_Getopt.ZeroArgs ((fun uu____2765  -> mk_bool true))),
        "Print full names (deprecated; use --print_full_names instead)");
      (FStar_Getopt.noshort, "query_stats",
        (FStar_Getopt.ZeroArgs ((fun uu____2779  -> mk_bool true))),
        "Print SMT query statistics");
      (FStar_Getopt.noshort, "record_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____2793  -> mk_bool true))),
        "Record a database of hints for efficient proof replay");
      (FStar_Getopt.noshort, "reuse_hint_for",
        (FStar_Getopt.OneArg
           (mk_string, "top-level name in the current module")),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");
      (FStar_Getopt.noshort, "show_signatures",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2825 =
                  let uu____2828 =
                    let uu____2831 = get_show_signatures ()  in x ::
                      uu____2831
                     in
                  FStar_All.pipe_right uu____2828 (FStar_List.map mk_string)
                   in
                mk_list uu____2825)), "[module name]")),
        "Show the checked signatures for all top-level symbols in the module");
      (FStar_Getopt.noshort, "silent",
        (FStar_Getopt.ZeroArgs ((fun uu____2851  -> mk_bool true))), " ");
      (FStar_Getopt.noshort, "smt",
        (FStar_Getopt.OneArg (mk_path, "[path]")),
        "Path to the Z3 SMT solver (we could eventually support other solvers)");
      (FStar_Getopt.noshort, "smtencoding.elim_box",
        (FStar_Getopt.OneArg
           ((string_as_bool "smtencoding.elim_box"), "true|false")),
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");
      (FStar_Getopt.noshort, "smtencoding.nl_arith_repr",
        (FStar_Getopt.OneArg (mk_string, "native|wrapped|boxwrap")),
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "smtencoding.l_arith_repr",
        (FStar_Getopt.OneArg (mk_string, "native|boxwrap")),
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "smt_solver",
        (FStar_Getopt.OneArg
           (((fun s  -> let uu____2925 = parse_solver s  in String uu____2925)),
             "[Z3|CVC4]")),
        "SMT solver in use (usually Z3, but could be CVC4)");
      (FStar_Getopt.noshort, "split_cases",
        (FStar_Getopt.OneArg
           (((fun n1  ->
                let uu____2943 = FStar_Util.int_of_string n1  in
                mk_int uu____2943)), "[positive integer]")),
        "Partition VC of a match into groups of [n] cases");
      (FStar_Getopt.noshort, "timing",
        (FStar_Getopt.ZeroArgs ((fun uu____2957  -> mk_bool true))),
        "Print the time it takes to verify each top-level definition");
      (FStar_Getopt.noshort, "trace_error",
        (FStar_Getopt.ZeroArgs ((fun uu____2971  -> mk_bool true))),
        "Don't print an error message; show an exception trace instead");
      (FStar_Getopt.noshort, "ugly",
        (FStar_Getopt.ZeroArgs ((fun uu____2985  -> mk_bool true))),
        "Emit output formatted for debugging");
      (FStar_Getopt.noshort, "unthrottle_inductives",
        (FStar_Getopt.ZeroArgs ((fun uu____2999  -> mk_bool true))),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
      (FStar_Getopt.noshort, "use_eq_at_higher_order",
        (FStar_Getopt.ZeroArgs ((fun uu____3013  -> mk_bool true))),
        "Use equality constraints when comparing higher-order types (Temporary)");
      (FStar_Getopt.noshort, "use_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____3027  -> mk_bool true))),
        "Use a previously recorded hints database for proof replay");
      (FStar_Getopt.noshort, "no_tactics",
        (FStar_Getopt.ZeroArgs ((fun uu____3041  -> mk_bool true))),
        "Do not run the tactic engine before discharging a VC");
      (FStar_Getopt.noshort, "using_facts_from",
        (FStar_Getopt.OneArg (cons_using_facts_from, "[namespace | fact id]")),
        "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids");
      (FStar_Getopt.noshort, "verify_all",
        (FStar_Getopt.ZeroArgs ((fun uu____3069  -> mk_bool true))),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");
      (FStar_Getopt.noshort, "verify_module",
        (FStar_Getopt.OneArg (cons_verify_module, "[module name]")),
        "Name of the module to verify");
      (FStar_Getopt.noshort, "__temp_no_proj",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____3101 =
                  let uu____3104 =
                    let uu____3107 = get___temp_no_proj ()  in x ::
                      uu____3107
                     in
                  FStar_All.pipe_right uu____3104 (FStar_List.map mk_string)
                   in
                mk_list uu____3101)), "[module name]")),
        "Don't generate projectors for this module");
      ('v', "version",
        (FStar_Getopt.ZeroArgs
           ((fun uu____3128  ->
               display_version (); FStar_All.exit (Prims.parse_int "0")))),
        "Display version number");
      (FStar_Getopt.noshort, "warn_default_effects",
        (FStar_Getopt.ZeroArgs ((fun uu____3143  -> mk_bool true))),
        "Warn when (a -> b) is desugared to (a -> Tot b)");
      (FStar_Getopt.noshort, "z3cliopt",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3161 =
                  let uu____3164 =
                    let uu____3167 = get_z3cliopt ()  in
                    FStar_List.append uu____3167 [s]  in
                  FStar_All.pipe_right uu____3164 (FStar_List.map mk_string)
                   in
                mk_list uu____3161)), "[option]")),
        "Z3 command line options");
      (FStar_Getopt.noshort, "z3refresh",
        (FStar_Getopt.ZeroArgs ((fun uu____3187  -> mk_bool true))),
        "Restart Z3 after each query; useful for ensuring proof robustness");
      (FStar_Getopt.noshort, "z3rlimit",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3205 = FStar_Util.int_of_string s  in
                mk_int uu____3205)), "[positive integer]")),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
      (FStar_Getopt.noshort, "z3rlimit_factor",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3223 = FStar_Util.int_of_string s  in
                mk_int uu____3223)), "[positive integer]")),
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");
      (FStar_Getopt.noshort, "z3seed",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3241 = FStar_Util.int_of_string s  in
                mk_int uu____3241)), "[positive integer]")),
        "Set the Z3 random seed (default 0)");
      (FStar_Getopt.noshort, "__no_positivity",
        (FStar_Getopt.ZeroArgs ((fun uu____3255  -> mk_bool true))),
        "Don't check positivity of inductive types");
      (FStar_Getopt.noshort, "__ml_no_eta_expand_coertions",
        (FStar_Getopt.ZeroArgs ((fun uu____3269  -> mk_bool true))),
        "Do not eta-expand coertions in generated OCaml")]
       in
    let uu____3280 = FStar_List.map mk_spec specs1  in
    ('h', "help",
      (FStar_Getopt.ZeroArgs
         (fun x  ->
            display_usage_aux specs1; FStar_All.exit (Prims.parse_int "0"))),
      "Display this information") :: uu____3280

and parse_codegen : Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Kremlin" -> s
    | "OCaml" -> s
    | "FSharp" -> s
    | uu____3320 ->
        (FStar_Util.print_string "Wrong argument to codegen flag\n";
         (let uu____3323 = specs ()  in display_usage_aux uu____3323);
         FStar_All.exit (Prims.parse_int "1"))

and parse_solver : Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Z3" -> s
    | "CVC4" -> s
    | "z3" -> s
    | "cvc4" -> s
    | uu____3337 ->
        (FStar_Util.print_string "Wrong argument to 'smt_solver' flag\n";
         (let uu____3340 = specs ()  in display_usage_aux uu____3340);
         FStar_All.exit (Prims.parse_int "1"))

and string_as_bool : Prims.string -> Prims.string -> option_val =
  fun option_name  ->
    fun uu___55_3354  ->
      match uu___55_3354 with
      | "true" -> mk_bool true
      | "false" -> mk_bool false
      | uu____3355 ->
          (FStar_Util.print1 "Wrong argument to %s\n" option_name;
           (let uu____3358 = specs ()  in display_usage_aux uu____3358);
           FStar_All.exit (Prims.parse_int "1"))

and validate_dir : Prims.string -> Prims.string =
  fun p  -> FStar_Util.mkdir false p; p

let docs :
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3382  ->
    let uu____3383 = specs ()  in
    FStar_List.map
      (fun uu____3415  ->
         match uu____3415 with
         | (uu____3430,name,uu____3432,doc) -> (name, doc)) uu____3383
  
let settable : Prims.string -> Prims.bool =
  fun uu___56_3441  ->
    match uu___56_3441 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "hide_genident_nums" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
    | "hint_file" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "inline_arith" -> true
    | "lax" -> true
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
    | "show_signatures" -> true
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
    | "using_facts_from" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | uu____3442 -> false
  
let resettable : Prims.string -> Prims.bool =
  fun s  -> ((settable s) || (s = "z3seed")) || (s = "z3cliopt") 
let all_specs : FStar_Getopt.opt Prims.list = specs () 
let settable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____3490  ->
          match uu____3490 with
          | (uu____3501,x,uu____3503,uu____3504) -> settable x))
  
let resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____3550  ->
          match uu____3550 with
          | (uu____3561,x,uu____3563,uu____3564) -> resettable x))
  
let display_usage : Prims.unit -> Prims.unit =
  fun uu____3572  ->
    let uu____3573 = specs ()  in display_usage_aux uu____3573
  
let fstar_home : Prims.unit -> Prims.string =
  fun uu____3589  ->
    let uu____3590 = get_fstar_home ()  in
    match uu____3590 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____3596 =
            let uu____3601 = mk_string x1  in ("fstar_home", uu____3601)  in
          set_option' uu____3596);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let uu___is_File_argument : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____3610 -> true
    | uu____3611 -> false
  
let __proj__File_argument__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____3619 -> uu____3619
  
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
          let uu____3665 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____3665
  
let file_list_ : Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____3688  ->
    let res =
      let uu____3690 = specs ()  in
      FStar_Getopt.parse_cmdline uu____3690
        (fun i  ->
           let uu____3696 =
             let uu____3699 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____3699 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____3696)
       in
    let uu____3738 =
      let uu____3741 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____3741
       in
    (res, uu____3738)
  
let file_list : Prims.unit -> Prims.string Prims.list =
  fun uu____3769  -> FStar_ST.op_Bang file_list_ 
let restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____3798 = specs ()  in
       FStar_Getopt.parse_cmdline uu____3798 (fun x  -> ())  in
     (let uu____3804 =
        let uu____3809 =
          let uu____3810 = FStar_List.map mk_string old_verify_module  in
          List uu____3810  in
        ("verify_module", uu____3809)  in
      set_option' uu____3804);
     r)
  
let should_verify : Prims.string -> Prims.bool =
  fun m  ->
    let uu____3817 = get_lax ()  in
    if uu____3817
    then false
    else
      (let uu____3819 = get_verify_all ()  in
       if uu____3819
       then true
       else
         (let uu____3821 = get_verify_module ()  in
          match uu____3821 with
          | [] ->
              let uu____3824 = file_list ()  in
              FStar_List.existsML
                (fun f  ->
                   let f1 = FStar_Util.basename f  in
                   let f2 =
                     let uu____3833 =
                       let uu____3834 =
                         let uu____3835 =
                           let uu____3836 = FStar_Util.get_file_extension f1
                              in
                           FStar_String.length uu____3836  in
                         (FStar_String.length f1) - uu____3835  in
                       uu____3834 - (Prims.parse_int "1")  in
                     FStar_String.substring f1 (Prims.parse_int "0")
                       uu____3833
                      in
                   (FStar_String.lowercase f2) = m) uu____3824
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
  
let dont_gen_projectors : Prims.string -> Prims.bool =
  fun m  ->
    let uu____3844 = get___temp_no_proj ()  in
    FStar_List.contains m uu____3844
  
let should_print_message : Prims.string -> Prims.bool =
  fun m  ->
    let uu____3851 = should_verify m  in
    if uu____3851 then m <> "Prims" else false
  
let include_path : Prims.unit -> Prims.string Prims.list =
  fun uu____3858  ->
    let uu____3859 = get_no_default_includes ()  in
    if uu____3859
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____3867 =
         let uu____3870 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____3870
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____3883 =
         let uu____3886 = get_include ()  in
         FStar_List.append uu____3886 ["."]  in
       FStar_List.append uu____3867 uu____3883)
  
let find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____3895 = FStar_Util.is_path_absolute filename  in
    if uu____3895
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____3902 =
         let uu____3905 = include_path ()  in FStar_List.rev uu____3905  in
       FStar_Util.find_map uu____3902
         (fun p  ->
            let path = FStar_Util.join_paths p filename  in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let prims : Prims.unit -> Prims.string =
  fun uu____3918  ->
    let uu____3919 = get_prims ()  in
    match uu____3919 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____3923 = find_file filename  in
        (match uu____3923 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____3927 =
               let uu____3928 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename
                  in
               FStar_Util.Failure uu____3928  in
             FStar_Exn.raise uu____3927)
    | FStar_Pervasives_Native.Some x -> x
  
let prims_basename : Prims.unit -> Prims.string =
  fun uu____3933  ->
    let uu____3934 = prims ()  in FStar_Util.basename uu____3934
  
let pervasives : Prims.unit -> Prims.string =
  fun uu____3938  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____3940 = find_file filename  in
    match uu____3940 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____3944 =
          let uu____3945 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename
             in
          FStar_Util.Failure uu____3945  in
        FStar_Exn.raise uu____3944
  
let pervasives_basename : Prims.unit -> Prims.string =
  fun uu____3949  ->
    let uu____3950 = pervasives ()  in FStar_Util.basename uu____3950
  
let pervasives_native_basename : Prims.unit -> Prims.string =
  fun uu____3954  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____3956 = find_file filename  in
    match uu____3956 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____3960 =
          let uu____3961 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename
             in
          FStar_Util.Failure uu____3961  in
        FStar_Exn.raise uu____3960
  
let prepend_output_dir : Prims.string -> Prims.string =
  fun fname  ->
    let uu____3966 = get_odir ()  in
    match uu____3966 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
  
let __temp_no_proj : Prims.string -> Prims.bool =
  fun s  ->
    let uu____3974 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____3974 (FStar_List.contains s)
  
let admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____3982  -> get_admit_smt_queries () 
let admit_except : Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____3988  -> get_admit_except () 
let codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____3994  -> get_codegen () 
let codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____4002  ->
    let uu____4003 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____4003
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let debug_any : Prims.unit -> Prims.bool =
  fun uu____4019  -> let uu____4020 = get_debug ()  in uu____4020 <> [] 
let debug_at_level : Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____4035 = get_debug ()  in
       FStar_All.pipe_right uu____4035 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____4045  -> get_dep () 
let detail_errors : Prims.unit -> Prims.bool =
  fun uu____4049  -> get_detail_errors () 
let detail_hint_replay : Prims.unit -> Prims.bool =
  fun uu____4053  -> get_detail_hint_replay () 
let doc : Prims.unit -> Prims.bool = fun uu____4057  -> get_doc () 
let dump_module : Prims.string -> Prims.bool =
  fun s  ->
    let uu____4062 = get_dump_module ()  in
    FStar_All.pipe_right uu____4062 (FStar_List.contains s)
  
let eager_inference : Prims.unit -> Prims.bool =
  fun uu____4070  -> get_eager_inference () 
let explicit_deps : Prims.unit -> Prims.bool =
  fun uu____4074  -> get_explicit_deps () 
let extract_all : Prims.unit -> Prims.bool =
  fun uu____4078  -> get_extract_all () 
let fs_typ_app : Prims.string -> Prims.bool =
  fun filename  ->
    let uu____4083 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____4083
  
let full_context_dependency : Prims.unit -> Prims.bool =
  fun uu____4107  -> true 
let hide_genident_nums : Prims.unit -> Prims.bool =
  fun uu____4111  -> get_hide_genident_nums () 
let hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____4115  -> get_hide_uvar_nums () 
let hint_info : Prims.unit -> Prims.bool =
  fun uu____4119  -> (get_hint_info ()) || (get_query_stats ()) 
let hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____4125  -> get_hint_file () 
let ide : Prims.unit -> Prims.bool = fun uu____4129  -> get_ide () 
let indent : Prims.unit -> Prims.bool = fun uu____4133  -> get_indent () 
let initial_fuel : Prims.unit -> Prims.int =
  fun uu____4137  ->
    let uu____4138 = get_initial_fuel ()  in
    let uu____4139 = get_max_fuel ()  in Prims.min uu____4138 uu____4139
  
let initial_ifuel : Prims.unit -> Prims.int =
  fun uu____4143  ->
    let uu____4144 = get_initial_ifuel ()  in
    let uu____4145 = get_max_ifuel ()  in Prims.min uu____4144 uu____4145
  
let interactive : Prims.unit -> Prims.bool =
  fun uu____4149  -> (get_in ()) || (get_ide ()) 
let lax : Prims.unit -> Prims.bool = fun uu____4153  -> get_lax () 
let load : Prims.unit -> Prims.string Prims.list =
  fun uu____4159  -> get_load () 
let legacy_interactive : Prims.unit -> Prims.bool =
  fun uu____4163  -> get_in () 
let log_queries : Prims.unit -> Prims.bool =
  fun uu____4167  -> get_log_queries () 
let log_types : Prims.unit -> Prims.bool =
  fun uu____4171  -> get_log_types () 
let max_fuel : Prims.unit -> Prims.int = fun uu____4175  -> get_max_fuel () 
let max_ifuel : Prims.unit -> Prims.int = fun uu____4179  -> get_max_ifuel () 
let min_fuel : Prims.unit -> Prims.int = fun uu____4183  -> get_min_fuel () 
let ml_ish : Prims.unit -> Prims.bool = fun uu____4187  -> get_MLish () 
let set_ml_ish : Prims.unit -> Prims.unit =
  fun uu____4191  -> set_option "MLish" (Bool true) 
let n_cores : Prims.unit -> Prims.int = fun uu____4195  -> get_n_cores () 
let no_default_includes : Prims.unit -> Prims.bool =
  fun uu____4199  -> get_no_default_includes () 
let no_extract : Prims.string -> Prims.bool =
  fun s  ->
    let uu____4204 = get_no_extract ()  in
    FStar_All.pipe_right uu____4204 (FStar_List.contains s)
  
let no_location_info : Prims.unit -> Prims.bool =
  fun uu____4212  -> get_no_location_info () 
let output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____4218  -> get_odir () 
let ugly : Prims.unit -> Prims.bool = fun uu____4222  -> get_ugly () 
let print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____4226  -> get_print_bound_var_types () 
let print_effect_args : Prims.unit -> Prims.bool =
  fun uu____4230  -> get_print_effect_args () 
let print_implicits : Prims.unit -> Prims.bool =
  fun uu____4234  -> get_print_implicits () 
let print_real_names : Prims.unit -> Prims.bool =
  fun uu____4238  -> (get_prn ()) || (get_print_full_names ()) 
let print_universes : Prims.unit -> Prims.bool =
  fun uu____4242  -> get_print_universes () 
let print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____4246  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let query_stats : Prims.unit -> Prims.bool =
  fun uu____4250  -> get_query_stats () 
let record_hints : Prims.unit -> Prims.bool =
  fun uu____4254  -> get_record_hints () 
let reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____4260  -> get_reuse_hint_for () 
let silent : Prims.unit -> Prims.bool = fun uu____4264  -> get_silent () 
let smtencoding_elim_box : Prims.unit -> Prims.bool =
  fun uu____4268  -> get_smtencoding_elim_box () 
let smtencoding_nl_arith_native : Prims.unit -> Prims.bool =
  fun uu____4272  ->
    let uu____4273 = get_smtencoding_nl_arith_repr ()  in
    uu____4273 = "native"
  
let smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool =
  fun uu____4277  ->
    let uu____4278 = get_smtencoding_nl_arith_repr ()  in
    uu____4278 = "wrapped"
  
let smtencoding_nl_arith_default : Prims.unit -> Prims.bool =
  fun uu____4282  ->
    let uu____4283 = get_smtencoding_nl_arith_repr ()  in
    uu____4283 = "boxwrap"
  
let smtencoding_l_arith_native : Prims.unit -> Prims.bool =
  fun uu____4287  ->
    let uu____4288 = get_smtencoding_l_arith_repr ()  in
    uu____4288 = "native"
  
let smtencoding_l_arith_default : Prims.unit -> Prims.bool =
  fun uu____4292  ->
    let uu____4293 = get_smtencoding_l_arith_repr ()  in
    uu____4293 = "boxwrap"
  
let smt_solver : Prims.unit -> solver =
  fun uu____4297  ->
    let uu____4298 = get_smtsolver ()  in
    match uu____4298 with
    | "z3" -> Z3
    | "Z3" -> Z3
    | "cvc4" -> CVC4
    | "CVC4" -> CVC4
    | uu____4299 -> failwith "Invalid SMT solver"
  
let split_cases : Prims.unit -> Prims.int =
  fun uu____4303  -> get_split_cases () 
let timing : Prims.unit -> Prims.bool = fun uu____4307  -> get_timing () 
let trace_error : Prims.unit -> Prims.bool =
  fun uu____4311  -> get_trace_error () 
let unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____4315  -> get_unthrottle_inductives () 
let use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____4319  -> get_use_eq_at_higher_order () 
let use_hints : Prims.unit -> Prims.bool =
  fun uu____4323  -> get_use_hints () 
let use_tactics : Prims.unit -> Prims.bool =
  fun uu____4327  -> get_use_tactics () 
let using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____4335  -> get_using_facts_from () 
let verify_all : Prims.unit -> Prims.bool =
  fun uu____4339  -> get_verify_all () 
let verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____4345  -> get_verify_module () 
let warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____4349  -> get_warn_default_effects () 
let solver_exe : Prims.unit -> Prims.string =
  fun uu____4353  ->
    let uu____4354 = get_smt ()  in
    match uu____4354 with
    | FStar_Pervasives_Native.None  ->
        let uu____4357 =
          let uu____4358 = smt_solver ()  in
          match uu____4358 with | Z3  -> "z3" | CVC4  -> "cvc4"  in
        FStar_All.pipe_right uu____4357 FStar_Platform.exe
    | FStar_Pervasives_Native.Some s -> s
  
let z3_cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____4365  -> get_z3cliopt () 
let z3_refresh : Prims.unit -> Prims.bool =
  fun uu____4369  -> get_z3refresh () 
let z3_rlimit : Prims.unit -> Prims.int = fun uu____4373  -> get_z3rlimit () 
let z3_rlimit_factor : Prims.unit -> Prims.int =
  fun uu____4377  -> get_z3rlimit_factor () 
let z3_seed : Prims.unit -> Prims.int = fun uu____4381  -> get_z3seed () 
let no_positivity : Prims.unit -> Prims.bool =
  fun uu____4385  -> get_no_positivity () 
let ml_no_eta_expand_coertions : Prims.unit -> Prims.bool =
  fun uu____4389  -> get_ml_no_eta_expand_coertions () 
let should_extract : Prims.string -> Prims.bool =
  fun m  ->
    (let uu____4396 = no_extract m  in Prims.op_Negation uu____4396) &&
      ((extract_all ()) ||
         (let uu____4399 = get_extract_module ()  in
          match uu____4399 with
          | [] ->
              let uu____4402 = get_extract_namespace ()  in
              (match uu____4402 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
  