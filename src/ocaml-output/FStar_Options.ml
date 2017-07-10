open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
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
  | Unset 
let uu___is_Bool : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____58 -> false
  
let __proj__Bool__item___0 : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let uu___is_String : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____70 -> false
  
let __proj__String__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0 
let uu___is_Path : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____82 -> false
  
let __proj__Path__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0 
let uu___is_Int : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Int _0 -> true | uu____94 -> false 
let __proj__Int__item___0 : option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0 
let uu___is_List : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____107 -> false
  
let __proj__List__item___0 : option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0 
let uu___is_Unset : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____121 -> false
  
type options =
  | Set 
  | Reset 
  | Restore 
let uu___is_Set : options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____125 -> false 
let uu___is_Reset : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____129 -> false
  
let uu___is_Restore : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____133 -> false
  
let __unit_tests__ : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let __unit_tests : Prims.unit -> Prims.bool =
  fun uu____139  -> FStar_ST.read __unit_tests__ 
let __set_unit_tests : Prims.unit -> Prims.unit =
  fun uu____144  -> FStar_ST.write __unit_tests__ true 
let __clear_unit_tests : Prims.unit -> Prims.unit =
  fun uu____149  -> FStar_ST.write __unit_tests__ false 
let as_bool : option_val -> Prims.bool =
  fun uu___49_154  ->
    match uu___49_154 with
    | Bool b -> b
    | uu____156 -> failwith "Impos: expected Bool"
  
let as_int : option_val -> Prims.int =
  fun uu___50_159  ->
    match uu___50_159 with
    | Int b -> b
    | uu____161 -> failwith "Impos: expected Int"
  
let as_string : option_val -> Prims.string =
  fun uu___51_164  ->
    match uu___51_164 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____167 -> failwith "Impos: expected String"
  
let as_list as_t uu___52_183 =
  match uu___52_183 with
  | List ts -> FStar_All.pipe_right ts (FStar_List.map as_t)
  | uu____190 -> failwith "Impos: expected List" 
let as_option as_t uu___53_207 =
  match uu___53_207 with
  | Unset  -> FStar_Pervasives_Native.None
  | v1 -> let uu____211 = as_t v1  in FStar_Pervasives_Native.Some uu____211 
let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let peek : Prims.unit -> option_val FStar_Util.smap =
  fun uu____223  ->
    let uu____224 = FStar_ST.read fstar_options  in FStar_List.hd uu____224
  
let pop : Prims.unit -> Prims.unit =
  fun uu____234  ->
    let uu____235 = FStar_ST.read fstar_options  in
    match uu____235 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____243::[] -> failwith "TOO MANY POPS!"
    | uu____247::tl1 -> FStar_ST.write fstar_options tl1
  
let push : Prims.unit -> Prims.unit =
  fun uu____259  ->
    let uu____260 =
      let uu____263 =
        let uu____265 = peek ()  in FStar_Util.smap_copy uu____265  in
      let uu____267 = FStar_ST.read fstar_options  in uu____263 :: uu____267
       in
    FStar_ST.write fstar_options uu____260
  
let set_option : Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____285 = peek ()  in FStar_Util.smap_add uu____285 k v1
  
let set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____291  -> match uu____291 with | (k,v1) -> set_option k v1 
let with_saved_options f = push (); (let retv = f ()  in pop (); retv) 
let light_off_files : Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let add_light_off_file : Prims.string -> Prims.unit =
  fun filename  ->
    let uu____319 =
      let uu____321 = FStar_ST.read light_off_files  in filename :: uu____321
       in
    FStar_ST.write light_off_files uu____319
  
let defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
  ("check_hints", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("dep", Unset);
  ("detail_errors", (Bool false));
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
  ("lax_except", Unset);
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
  ("print_fuels", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("show_signatures", (List []));
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
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
  ("z3timeout", (Int (Prims.parse_int "5")));
  ("z3cliopt", (List []));
  ("__no_positivity", (Bool false))] 
let init : Prims.unit -> Prims.unit =
  fun uu____502  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let clear : Prims.unit -> Prims.unit =
  fun uu____513  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.write fstar_options [o];
    FStar_ST.write light_off_files [];
    init ()
  
let _run : Prims.unit = clear () 
let get_option : Prims.string -> option_val =
  fun s  ->
    let uu____530 =
      let uu____532 = peek ()  in FStar_Util.smap_try_find uu____532 s  in
    match uu____530 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt s c = c (get_option s) 
let get_admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____554  -> lookup_opt "admit_smt_queries" as_bool 
let get_check_hints : Prims.unit -> Prims.bool =
  fun uu____557  -> lookup_opt "check_hints" as_bool 
let get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____561  -> lookup_opt "codegen" (as_option as_string) 
let get_codegen_lib : Prims.unit -> Prims.string Prims.list =
  fun uu____566  -> lookup_opt "codegen-lib" (as_list as_string) 
let get_debug : Prims.unit -> Prims.string Prims.list =
  fun uu____571  -> lookup_opt "debug" (as_list as_string) 
let get_debug_level : Prims.unit -> Prims.string Prims.list =
  fun uu____576  -> lookup_opt "debug_level" (as_list as_string) 
let get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____581  -> lookup_opt "dep" (as_option as_string) 
let get_detail_errors : Prims.unit -> Prims.bool =
  fun uu____585  -> lookup_opt "detail_errors" as_bool 
let get_doc : Prims.unit -> Prims.bool =
  fun uu____588  -> lookup_opt "doc" as_bool 
let get_dump_module : Prims.unit -> Prims.string Prims.list =
  fun uu____592  -> lookup_opt "dump_module" (as_list as_string) 
let get_eager_inference : Prims.unit -> Prims.bool =
  fun uu____596  -> lookup_opt "eager_inference" as_bool 
let get_explicit_deps : Prims.unit -> Prims.bool =
  fun uu____599  -> lookup_opt "explicit_deps" as_bool 
let get_extract_all : Prims.unit -> Prims.bool =
  fun uu____602  -> lookup_opt "extract_all" as_bool 
let get_extract_module : Prims.unit -> Prims.string Prims.list =
  fun uu____606  -> lookup_opt "extract_module" (as_list as_string) 
let get_extract_namespace : Prims.unit -> Prims.string Prims.list =
  fun uu____611  -> lookup_opt "extract_namespace" (as_list as_string) 
let get_fs_typ_app : Prims.unit -> Prims.bool =
  fun uu____615  -> lookup_opt "fs_typ_app" as_bool 
let get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____619  -> lookup_opt "fstar_home" (as_option as_string) 
let get_hide_genident_nums : Prims.unit -> Prims.bool =
  fun uu____623  -> lookup_opt "hide_genident_nums" as_bool 
let get_hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____626  -> lookup_opt "hide_uvar_nums" as_bool 
let get_hint_info : Prims.unit -> Prims.bool =
  fun uu____629  -> lookup_opt "hint_info" as_bool 
let get_hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____633  -> lookup_opt "hint_file" (as_option as_string) 
let get_in : Prims.unit -> Prims.bool =
  fun uu____637  -> lookup_opt "in" as_bool 
let get_ide : Prims.unit -> Prims.bool =
  fun uu____640  -> lookup_opt "ide" as_bool 
let get_include : Prims.unit -> Prims.string Prims.list =
  fun uu____644  -> lookup_opt "include" (as_list as_string) 
let get_indent : Prims.unit -> Prims.bool =
  fun uu____648  -> lookup_opt "indent" as_bool 
let get_initial_fuel : Prims.unit -> Prims.int =
  fun uu____651  -> lookup_opt "initial_fuel" as_int 
let get_initial_ifuel : Prims.unit -> Prims.int =
  fun uu____654  -> lookup_opt "initial_ifuel" as_int 
let get_lax : Prims.unit -> Prims.bool =
  fun uu____657  -> lookup_opt "lax" as_bool 
let get_lax_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____661  -> lookup_opt "lax_except" (as_option as_string) 
let get_log_queries : Prims.unit -> Prims.bool =
  fun uu____665  -> lookup_opt "log_queries" as_bool 
let get_log_types : Prims.unit -> Prims.bool =
  fun uu____668  -> lookup_opt "log_types" as_bool 
let get_max_fuel : Prims.unit -> Prims.int =
  fun uu____671  -> lookup_opt "max_fuel" as_int 
let get_max_ifuel : Prims.unit -> Prims.int =
  fun uu____674  -> lookup_opt "max_ifuel" as_int 
let get_min_fuel : Prims.unit -> Prims.int =
  fun uu____677  -> lookup_opt "min_fuel" as_int 
let get_MLish : Prims.unit -> Prims.bool =
  fun uu____680  -> lookup_opt "MLish" as_bool 
let get_n_cores : Prims.unit -> Prims.int =
  fun uu____683  -> lookup_opt "n_cores" as_int 
let get_no_default_includes : Prims.unit -> Prims.bool =
  fun uu____686  -> lookup_opt "no_default_includes" as_bool 
let get_no_extract : Prims.unit -> Prims.string Prims.list =
  fun uu____690  -> lookup_opt "no_extract" (as_list as_string) 
let get_no_location_info : Prims.unit -> Prims.bool =
  fun uu____694  -> lookup_opt "no_location_info" as_bool 
let get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____698  -> lookup_opt "odir" (as_option as_string) 
let get_ugly : Prims.unit -> Prims.bool =
  fun uu____702  -> lookup_opt "ugly" as_bool 
let get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____706  -> lookup_opt "prims" (as_option as_string) 
let get_print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____710  -> lookup_opt "print_bound_var_types" as_bool 
let get_print_effect_args : Prims.unit -> Prims.bool =
  fun uu____713  -> lookup_opt "print_effect_args" as_bool 
let get_print_fuels : Prims.unit -> Prims.bool =
  fun uu____716  -> lookup_opt "print_fuels" as_bool 
let get_print_full_names : Prims.unit -> Prims.bool =
  fun uu____719  -> lookup_opt "print_full_names" as_bool 
let get_print_implicits : Prims.unit -> Prims.bool =
  fun uu____722  -> lookup_opt "print_implicits" as_bool 
let get_print_universes : Prims.unit -> Prims.bool =
  fun uu____725  -> lookup_opt "print_universes" as_bool 
let get_print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____728  -> lookup_opt "print_z3_statistics" as_bool 
let get_prn : Prims.unit -> Prims.bool =
  fun uu____731  -> lookup_opt "prn" as_bool 
let get_record_hints : Prims.unit -> Prims.bool =
  fun uu____734  -> lookup_opt "record_hints" as_bool 
let get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____738  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let get_show_signatures : Prims.unit -> Prims.string Prims.list =
  fun uu____743  -> lookup_opt "show_signatures" (as_list as_string) 
let get_silent : Prims.unit -> Prims.bool =
  fun uu____747  -> lookup_opt "silent" as_bool 
let get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____751  -> lookup_opt "smt" (as_option as_string) 
let get_smtencoding_elim_box : Prims.unit -> Prims.bool =
  fun uu____755  -> lookup_opt "smtencoding.elim_box" as_bool 
let get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string =
  fun uu____758  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let get_smtencoding_l_arith_repr : Prims.unit -> Prims.string =
  fun uu____761  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let get_split_cases : Prims.unit -> Prims.int =
  fun uu____764  -> lookup_opt "split_cases" as_int 
let get_timing : Prims.unit -> Prims.bool =
  fun uu____767  -> lookup_opt "timing" as_bool 
let get_trace_error : Prims.unit -> Prims.bool =
  fun uu____770  -> lookup_opt "trace_error" as_bool 
let get_unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____773  -> lookup_opt "unthrottle_inductives" as_bool 
let get_use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____776  -> lookup_opt "use_eq_at_higher_order" as_bool 
let get_use_hints : Prims.unit -> Prims.bool =
  fun uu____779  -> lookup_opt "use_hints" as_bool 
let get_use_tactics : Prims.unit -> Prims.bool =
  fun uu____782  ->
    let uu____783 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____783
  
let get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____788  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let get_verify_all : Prims.unit -> Prims.bool =
  fun uu____794  -> lookup_opt "verify_all" as_bool 
let get_verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____798  -> lookup_opt "verify_module" (as_list as_string) 
let get___temp_no_proj : Prims.unit -> Prims.string Prims.list =
  fun uu____803  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let get_version : Prims.unit -> Prims.bool =
  fun uu____807  -> lookup_opt "version" as_bool 
let get_warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____810  -> lookup_opt "warn_default_effects" as_bool 
let get_z3cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____814  -> lookup_opt "z3cliopt" (as_list as_string) 
let get_z3refresh : Prims.unit -> Prims.bool =
  fun uu____818  -> lookup_opt "z3refresh" as_bool 
let get_z3rlimit : Prims.unit -> Prims.int =
  fun uu____821  -> lookup_opt "z3rlimit" as_int 
let get_z3rlimit_factor : Prims.unit -> Prims.int =
  fun uu____824  -> lookup_opt "z3rlimit_factor" as_int 
let get_z3seed : Prims.unit -> Prims.int =
  fun uu____827  -> lookup_opt "z3seed" as_int 
let get_z3timeout : Prims.unit -> Prims.int =
  fun uu____830  -> lookup_opt "z3timeout" as_int 
let get_no_positivity : Prims.unit -> Prims.bool =
  fun uu____833  -> lookup_opt "__no_positivity" as_bool 
let dlevel : Prims.string -> debug_level_t =
  fun uu___54_836  ->
    match uu___54_836 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____844 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let debug_level_geq : debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____848 = get_debug_level ()  in
    FStar_All.pipe_right uu____848
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let universe_include_path_base_dirs : Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"] 
let _version : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _platform : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _compiler : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _date : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _commit : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let display_version : Prims.unit -> Prims.unit =
  fun uu____875  ->
    let uu____876 =
      let uu____877 = FStar_ST.read _version  in
      let uu____880 = FStar_ST.read _platform  in
      let uu____883 = FStar_ST.read _compiler  in
      let uu____886 = FStar_ST.read _date  in
      let uu____889 = FStar_ST.read _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____877
        uu____880 uu____883 uu____886 uu____889
       in
    FStar_Util.print_string uu____876
  
let display_usage_aux specs =
  FStar_Util.print_string "fstar.exe [options] file[s]\n";
  FStar_List.iter
    (fun uu____919  ->
       match uu____919 with
       | (uu____925,flag,p,doc) ->
           (match p with
            | FStar_Getopt.ZeroArgs ig ->
                if doc = ""
                then
                  let uu____934 =
                    let uu____935 = FStar_Util.colorize_bold flag  in
                    FStar_Util.format1 "  --%s\n" uu____935  in
                  FStar_Util.print_string uu____934
                else
                  (let uu____937 =
                     let uu____938 = FStar_Util.colorize_bold flag  in
                     FStar_Util.format2 "  --%s  %s\n" uu____938 doc  in
                   FStar_Util.print_string uu____937)
            | FStar_Getopt.OneArg (uu____939,argname) ->
                if doc = ""
                then
                  let uu____945 =
                    let uu____946 = FStar_Util.colorize_bold flag  in
                    let uu____947 = FStar_Util.colorize_bold argname  in
                    FStar_Util.format2 "  --%s %s\n" uu____946 uu____947  in
                  FStar_Util.print_string uu____945
                else
                  (let uu____949 =
                     let uu____950 = FStar_Util.colorize_bold flag  in
                     let uu____951 = FStar_Util.colorize_bold argname  in
                     FStar_Util.format3 "  --%s %s  %s\n" uu____950 uu____951
                       doc
                      in
                   FStar_Util.print_string uu____949))) specs
  
let mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____965 = o  in
    match uu____965 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____986 =
                let uu____987 = let uu____990 = f ()  in (name, uu____990)
                   in
                set_option' uu____987  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x =
                let uu____1001 = let uu____1004 = f x  in (name, uu____1004)
                   in
                set_option' uu____1001  in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let cons_extract_module : Prims.string -> option_val =
  fun s  ->
    let uu____1011 =
      let uu____1013 =
        let uu____1015 = get_extract_module ()  in (FStar_String.lowercase s)
          :: uu____1015
         in
      FStar_All.pipe_right uu____1013
        (FStar_List.map (fun _0_26  -> String _0_26))
       in
    List uu____1011
  
let cons_extract_namespace : Prims.string -> option_val =
  fun s  ->
    let uu____1022 =
      let uu____1024 =
        let uu____1026 = get_extract_namespace ()  in
        (FStar_String.lowercase s) :: uu____1026  in
      FStar_All.pipe_right uu____1024
        (FStar_List.map (fun _0_27  -> String _0_27))
       in
    List uu____1022
  
let add_extract_module : Prims.string -> Prims.unit =
  fun s  ->
    let uu____1033 = cons_extract_module s  in
    set_option "extract_module" uu____1033
  
let add_extract_namespace : Prims.string -> Prims.unit =
  fun s  ->
    let uu____1037 = cons_extract_namespace s  in
    set_option "extract_namespace" uu____1037
  
let cons_verify_module : Prims.string -> option_val =
  fun s  ->
    let uu____1041 =
      let uu____1043 =
        let uu____1045 = get_verify_module ()  in (FStar_String.lowercase s)
          :: uu____1045
         in
      FStar_All.pipe_right uu____1043
        (FStar_List.map (fun _0_28  -> String _0_28))
       in
    List uu____1041
  
let cons_using_facts_from : Prims.string -> option_val =
  fun s  ->
    set_option "z3refresh" (Bool true);
    (let uu____1053 = get_using_facts_from ()  in
     match uu____1053 with
     | FStar_Pervasives_Native.None  -> List [String s]
     | FStar_Pervasives_Native.Some l ->
         let uu____1060 =
           FStar_List.map (fun _0_29  -> String _0_29) (s :: l)  in
         List uu____1060)
  
let add_verify_module : Prims.string -> Prims.unit =
  fun s  ->
    let uu____1065 = cons_verify_module s  in
    set_option "verify_module" uu____1065
  
let rec specs :
  Prims.unit ->
    (FStar_Char.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____1077  ->
    let specs1 =
      [(FStar_Getopt.noshort, "admit_smt_queries",
         (FStar_Getopt.OneArg
            (((fun s  ->
                 if s = "true"
                 then Bool true
                 else
                   if s = "false"
                   then Bool false
                   else failwith "Invalid argument to --admit_smt_queries")),
              "[true|false]")),
         "Admit SMT queries, unsafe! (default 'false')");
      (FStar_Getopt.noshort, "codegen",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1106 = parse_codegen s  in String uu____1106)),
             "[OCaml|FSharp|Kremlin]")), "Generate code for execution");
      (FStar_Getopt.noshort, "codegen-lib",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1116 =
                  let uu____1118 =
                    let uu____1120 = get_codegen_lib ()  in s :: uu____1120
                     in
                  FStar_All.pipe_right uu____1118
                    (FStar_List.map (fun _0_30  -> String _0_30))
                   in
                List uu____1116)), "[namespace]")),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
      (FStar_Getopt.noshort, "debug",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1133 =
                  let uu____1135 =
                    let uu____1137 = get_debug ()  in x :: uu____1137  in
                  FStar_All.pipe_right uu____1135
                    (FStar_List.map (fun _0_31  -> String _0_31))
                   in
                List uu____1133)), "[module name]")),
        "Print lots of debugging information while checking module");
      (FStar_Getopt.noshort, "debug_level",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1150 =
                  let uu____1152 =
                    let uu____1154 = get_debug_level ()  in x :: uu____1154
                     in
                  FStar_All.pipe_right uu____1152
                    (FStar_List.map (fun _0_32  -> String _0_32))
                   in
                List uu____1150)), "[Low|Medium|High|Extreme|...]")),
        "Control the verbosity of debugging info");
      (FStar_Getopt.noshort, "dep",
        (FStar_Getopt.OneArg
           (((fun x  ->
                if (x = "make") || (x = "graph")
                then String x
                else failwith "invalid argument to 'dep'")), "[make|graph]")),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");
      (FStar_Getopt.noshort, "detail_errors",
        (FStar_Getopt.ZeroArgs ((fun uu____1174  -> Bool true))),
        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "doc",
        (FStar_Getopt.ZeroArgs ((fun uu____1181  -> Bool true))),
        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");
      (FStar_Getopt.noshort, "dump_module",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1191 =
                  let uu____1193 =
                    let uu____1195 = get_dump_module ()  in x :: uu____1195
                     in
                  FStar_All.pipe_right uu____1193
                    (FStar_List.map (fun _0_33  -> String _0_33))
                   in
                FStar_All.pipe_right uu____1191 (fun _0_34  -> List _0_34))),
             "[module name]")), "");
      (FStar_Getopt.noshort, "eager_inference",
        (FStar_Getopt.ZeroArgs ((fun uu____1206  -> Bool true))),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
      (FStar_Getopt.noshort, "explicit_deps",
        (FStar_Getopt.ZeroArgs ((fun uu____1213  -> Bool true))),
        "Do not find dependencies automatically, the user provides them on the command-line");
      (FStar_Getopt.noshort, "extract_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1220  -> Bool true))),
        "Discover the complete dependency graph and do not stop at interface boundaries");
      (FStar_Getopt.noshort, "extract_module",
        (FStar_Getopt.OneArg (cons_extract_module, "[module name]")),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");
      (FStar_Getopt.noshort, "extract_namespace",
        (FStar_Getopt.OneArg (cons_extract_namespace, "[namespace name]")),
        "Only extract modules in the specified namespace");
      (FStar_Getopt.noshort, "fstar_home",
        (FStar_Getopt.OneArg (((fun _0_35  -> Path _0_35)), "[dir]")),
        "Set the FSTAR_HOME variable to [dir]");
      (FStar_Getopt.noshort, "hide_genident_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1251  -> Bool true))),
        "Don't print generated identifier numbers");
      (FStar_Getopt.noshort, "hide_uvar_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1258  -> Bool true))),
        "Don't print unification variable numbers");
      (FStar_Getopt.noshort, "hint_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1265  -> Bool true))),
        "Print information regarding hints");
      (FStar_Getopt.noshort, "hint_file",
        (FStar_Getopt.OneArg (((fun _0_36  -> Path _0_36)), "[path]")),
        "Read/write hints to <path> (instead of module-specific hints files)");
      (FStar_Getopt.noshort, "in",
        (FStar_Getopt.ZeroArgs ((fun uu____1280  -> Bool true))),
        "Legacy interactive mode; reads input from stdin");
      (FStar_Getopt.noshort, "ide",
        (FStar_Getopt.ZeroArgs ((fun uu____1287  -> Bool true))),
        "JSON-based interactive mode for IDEs");
      (FStar_Getopt.noshort, "include",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1297 =
                  let uu____1299 =
                    let uu____1301 = get_include ()  in
                    FStar_List.map (fun _0_37  -> String _0_37) uu____1301
                     in
                  FStar_List.append uu____1299 [Path s]  in
                List uu____1297)), "[path]")),
        "A directory in which to search for files included on the command line");
      (FStar_Getopt.noshort, "indent",
        (FStar_Getopt.ZeroArgs ((fun uu____1309  -> Bool true))),
        "Parses and outputs the files on the command line");
      (FStar_Getopt.noshort, "initial_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1319 = FStar_Util.int_of_string x  in
                Int uu____1319)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try initially (default 2)");
      (FStar_Getopt.noshort, "initial_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1329 = FStar_Util.int_of_string x  in
                Int uu____1329)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at first (default 1)");
      (FStar_Getopt.noshort, "inline_arith",
        (FStar_Getopt.ZeroArgs ((fun uu____1336  -> Bool true))),
        "Inline definitions of arithmetic functions in the SMT encoding");
      (FStar_Getopt.noshort, "lax",
        (FStar_Getopt.ZeroArgs ((fun uu____1343  -> Bool true))),
        "Run the lax-type checker only (admit all verification conditions)");
      (FStar_Getopt.noshort, "lax_except",
        (FStar_Getopt.OneArg (((fun _0_38  -> String _0_38)), "[id]")),
        "Run the lax-type checker only (admit all verification conditions), except on the query labelled <id>");
      (FStar_Getopt.noshort, "log_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1358  -> Bool true))),
        "Print types computed for data/val/let-bindings");
      (FStar_Getopt.noshort, "log_queries",
        (FStar_Getopt.ZeroArgs ((fun uu____1365  -> Bool true))),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");
      (FStar_Getopt.noshort, "max_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1375 = FStar_Util.int_of_string x  in
                Int uu____1375)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try at most (default 8)");
      (FStar_Getopt.noshort, "max_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1385 = FStar_Util.int_of_string x  in
                Int uu____1385)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at most (default 2)");
      (FStar_Getopt.noshort, "min_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1395 = FStar_Util.int_of_string x  in
                Int uu____1395)), "[non-negative integer]")),
        "Minimum number of unrolling of recursive functions to try (default 1)");
      (FStar_Getopt.noshort, "MLish",
        (FStar_Getopt.ZeroArgs ((fun uu____1402  -> Bool true))),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
      (FStar_Getopt.noshort, "n_cores",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1412 = FStar_Util.int_of_string x  in
                Int uu____1412)), "[positive integer]")),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");
      (FStar_Getopt.noshort, "no_default_includes",
        (FStar_Getopt.ZeroArgs ((fun uu____1419  -> Bool true))),
        "Ignore the default module search paths");
      (FStar_Getopt.noshort, "no_extract",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1429 =
                  let uu____1431 =
                    let uu____1433 = get_no_extract ()  in x :: uu____1433
                     in
                  FStar_All.pipe_right uu____1431
                    (FStar_List.map (fun _0_39  -> String _0_39))
                   in
                List uu____1429)), "[module name]")),
        "Do not extract code from this module");
      (FStar_Getopt.noshort, "no_location_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1443  -> Bool true))),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
      (FStar_Getopt.noshort, "odir",
        (FStar_Getopt.OneArg
           (((fun p  -> let uu____1453 = validate_dir p  in Path uu____1453)),
             "[dir]")), "Place output in directory [dir]");
      (FStar_Getopt.noshort, "prims",
        (FStar_Getopt.OneArg (((fun _0_40  -> String _0_40)), "file")), "");
      (FStar_Getopt.noshort, "print_bound_var_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1468  -> Bool true))),
        "Print the types of bound variables");
      (FStar_Getopt.noshort, "print_effect_args",
        (FStar_Getopt.ZeroArgs ((fun uu____1475  -> Bool true))),
        "Print inferred predicate transformers for all computation types");
      (FStar_Getopt.noshort, "print_fuels",
        (FStar_Getopt.ZeroArgs ((fun uu____1482  -> Bool true))),
        "Print the fuel amounts used for each successful query");
      (FStar_Getopt.noshort, "print_full_names",
        (FStar_Getopt.ZeroArgs ((fun uu____1489  -> Bool true))),
        "Print full names of variables");
      (FStar_Getopt.noshort, "print_implicits",
        (FStar_Getopt.ZeroArgs ((fun uu____1496  -> Bool true))),
        "Print implicit arguments");
      (FStar_Getopt.noshort, "print_universes",
        (FStar_Getopt.ZeroArgs ((fun uu____1503  -> Bool true))),
        "Print universes");
      (FStar_Getopt.noshort, "print_z3_statistics",
        (FStar_Getopt.ZeroArgs ((fun uu____1510  -> Bool true))),
        "Print Z3 statistics for each SMT query");
      (FStar_Getopt.noshort, "prn",
        (FStar_Getopt.ZeroArgs ((fun uu____1517  -> Bool true))),
        "Print full names (deprecated; use --print_full_names instead)");
      (FStar_Getopt.noshort, "record_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1524  -> Bool true))),
        "Record a database of hints for efficient proof replay");
      (FStar_Getopt.noshort, "check_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1531  -> Bool true))),
        "Check new hints for replayability");
      (FStar_Getopt.noshort, "reuse_hint_for",
        (FStar_Getopt.OneArg
           (((fun _0_41  -> String _0_41)),
             "top-level name in the current module")),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");
      (FStar_Getopt.noshort, "show_signatures",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1549 =
                  let uu____1551 =
                    let uu____1553 = get_show_signatures ()  in x ::
                      uu____1553
                     in
                  FStar_All.pipe_right uu____1551
                    (FStar_List.map (fun _0_42  -> String _0_42))
                   in
                List uu____1549)), "[module name]")),
        "Show the checked signatures for all top-level symbols in the module");
      (FStar_Getopt.noshort, "silent",
        (FStar_Getopt.ZeroArgs ((fun uu____1563  -> Bool true))), " ");
      (FStar_Getopt.noshort, "smt",
        (FStar_Getopt.OneArg (((fun _0_43  -> Path _0_43)), "[path]")),
        "Path to the Z3 SMT solver (we could eventually support other solvers)");
      (FStar_Getopt.noshort, "smtencoding.elim_box",
        (FStar_Getopt.OneArg
           ((string_as_bool "smtencoding.elim_box"), "true|false")),
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");
      (FStar_Getopt.noshort, "smtencoding.nl_arith_repr",
        (FStar_Getopt.OneArg
           (((fun _0_44  -> String _0_44)), "native|wrapped|boxwrap")),
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "smtencoding.l_arith_repr",
        (FStar_Getopt.OneArg
           (((fun _0_45  -> String _0_45)), "native|boxwrap")),
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "split_cases",
        (FStar_Getopt.OneArg
           (((fun n1  ->
                let uu____1605 = FStar_Util.int_of_string n1  in
                Int uu____1605)), "[positive integer]")),
        "Partition VC of a match into groups of [n] cases");
      (FStar_Getopt.noshort, "timing",
        (FStar_Getopt.ZeroArgs ((fun uu____1612  -> Bool true))),
        "Print the time it takes to verify each top-level definition");
      (FStar_Getopt.noshort, "trace_error",
        (FStar_Getopt.ZeroArgs ((fun uu____1619  -> Bool true))),
        "Don't print an error message; show an exception trace instead");
      (FStar_Getopt.noshort, "ugly",
        (FStar_Getopt.ZeroArgs ((fun uu____1626  -> Bool true))),
        "Emit output formatted for debugging");
      (FStar_Getopt.noshort, "unthrottle_inductives",
        (FStar_Getopt.ZeroArgs ((fun uu____1633  -> Bool true))),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
      (FStar_Getopt.noshort, "use_eq_at_higher_order",
        (FStar_Getopt.ZeroArgs ((fun uu____1640  -> Bool true))),
        "Use equality constraints when comparing higher-order types (Temporary)");
      (FStar_Getopt.noshort, "use_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1647  -> Bool true))),
        "Use a previously recorded hints database for proof replay");
      (FStar_Getopt.noshort, "no_tactics",
        (FStar_Getopt.ZeroArgs ((fun uu____1654  -> Bool true))),
        "Do not run the tactic engine before discharging a VC");
      (FStar_Getopt.noshort, "using_facts_from",
        (FStar_Getopt.OneArg (cons_using_facts_from, "[namespace | fact id]")),
        "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids");
      (FStar_Getopt.noshort, "verify_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1669  -> Bool true))),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");
      (FStar_Getopt.noshort, "verify_module",
        (FStar_Getopt.OneArg (cons_verify_module, "[module name]")),
        "Name of the module to verify");
      (FStar_Getopt.noshort, "__temp_no_proj",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1687 =
                  let uu____1689 =
                    let uu____1691 = get___temp_no_proj ()  in x ::
                      uu____1691
                     in
                  FStar_All.pipe_right uu____1689
                    (FStar_List.map (fun _0_46  -> String _0_46))
                   in
                List uu____1687)), "[module name]")),
        "Don't generate projectors for this module");
      ('v', "version",
        (FStar_Getopt.ZeroArgs
           ((fun uu____1701  ->
               display_version (); FStar_All.exit (Prims.parse_int "0")))),
        "Display version number");
      (FStar_Getopt.noshort, "warn_default_effects",
        (FStar_Getopt.ZeroArgs ((fun uu____1709  -> Bool true))),
        "Warn when (a -> b) is desugared to (a -> Tot b)");
      (FStar_Getopt.noshort, "z3cliopt",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1719 =
                  let uu____1721 =
                    let uu____1723 = get_z3cliopt ()  in
                    FStar_List.append uu____1723 [s]  in
                  FStar_All.pipe_right uu____1721
                    (FStar_List.map (fun _0_47  -> String _0_47))
                   in
                List uu____1719)), "[option]")), "Z3 command line options");
      (FStar_Getopt.noshort, "z3refresh",
        (FStar_Getopt.ZeroArgs ((fun uu____1733  -> Bool true))),
        "Restart Z3 after each query; useful for ensuring proof robustness");
      (FStar_Getopt.noshort, "z3rlimit",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1743 = FStar_Util.int_of_string s  in
                Int uu____1743)), "[positive integer]")),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
      (FStar_Getopt.noshort, "z3rlimit_factor",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1753 = FStar_Util.int_of_string s  in
                Int uu____1753)), "[positive integer]")),
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");
      (FStar_Getopt.noshort, "z3seed",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1763 = FStar_Util.int_of_string s  in
                Int uu____1763)), "[positive integer]")),
        "Set the Z3 random seed (default 0)");
      (FStar_Getopt.noshort, "z3timeout",
        (FStar_Getopt.OneArg
           (((fun s  ->
                FStar_Util.print_string
                  "Warning: z3timeout ignored; use z3rlimit instead\n";
                (let uu____1774 = FStar_Util.int_of_string s  in
                 Int uu____1774))), "[positive integer]")),
        "Set the Z3 per-query (soft) timeout to [t] seconds (default 5)");
      (FStar_Getopt.noshort, "__no_positivity",
        (FStar_Getopt.ZeroArgs ((fun uu____1781  -> Bool true))),
        "Don't check positivity of inductive types")]
       in
    let uu____1787 = FStar_List.map mk_spec specs1  in
    ('h', "help",
      (FStar_Getopt.ZeroArgs
         (fun x  ->
            display_usage_aux specs1; FStar_All.exit (Prims.parse_int "0"))),
      "Display this information") :: uu____1787

and parse_codegen : Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Kremlin" -> s
    | "OCaml" -> s
    | "FSharp" -> s
    | uu____1808 ->
        (FStar_Util.print_string "Wrong argument to codegen flag\n";
         (let uu____1811 = specs ()  in display_usage_aux uu____1811);
         FStar_All.exit (Prims.parse_int "1"))

and string_as_bool : Prims.string -> Prims.string -> option_val =
  fun option_name  ->
    fun uu___55_1819  ->
      match uu___55_1819 with
      | "true" -> Bool true
      | "false" -> Bool false
      | uu____1820 ->
          (FStar_Util.print1 "Wrong argument to %s\n" option_name;
           (let uu____1823 = specs ()  in display_usage_aux uu____1823);
           FStar_All.exit (Prims.parse_int "1"))

and validate_dir : Prims.string -> Prims.string =
  fun p  -> FStar_Util.mkdir false p; p

let docs :
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1837  ->
    let uu____1838 = specs ()  in
    FStar_List.map
      (fun uu____1852  ->
         match uu____1852 with
         | (uu____1860,name,uu____1862,doc) -> (name, doc)) uu____1838
  
let settable : Prims.string -> Prims.bool =
  fun uu___56_1868  ->
    match uu___56_1868 with
    | "admit_smt_queries" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "eager_inference" -> true
    | "hide_genident_nums" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
    | "hint_file" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "inline_arith" -> true
    | "lax" -> true
    | "lax_except" -> true
    | "log_types" -> true
    | "log_queries" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "ugly" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_fuels" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
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
    | uu____1869 -> false
  
let resettable : Prims.string -> Prims.bool =
  fun s  ->
    (((settable s) || (s = "z3timeout")) || (s = "z3seed")) ||
      (s = "z3cliopt")
  
let all_specs : FStar_Getopt.opt Prims.list = specs () 
let settable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____1892  ->
          match uu____1892 with
          | (uu____1898,x,uu____1900,uu____1901) -> settable x))
  
let resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____1922  ->
          match uu____1922 with
          | (uu____1928,x,uu____1930,uu____1931) -> resettable x))
  
let display_usage : Prims.unit -> Prims.unit =
  fun uu____1936  ->
    let uu____1937 = specs ()  in display_usage_aux uu____1937
  
let fstar_home : Prims.unit -> Prims.string =
  fun uu____1946  ->
    let uu____1947 = get_fstar_home ()  in
    match uu____1947 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        (set_option' ("fstar_home", (String x1)); x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let uu___is_File_argument : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____1959 -> true
    | uu____1960 -> false
  
let __proj__File_argument__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____1967 -> uu____1967
  
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
            (fun s1  -> raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____1993 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____1993
  
let file_list_ : Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____2004  ->
    let res =
      let uu____2006 = specs ()  in
      FStar_Getopt.parse_cmdline uu____2006
        (fun i  ->
           let uu____2009 =
             let uu____2011 = FStar_ST.read file_list_  in
             FStar_List.append uu____2011 [i]  in
           FStar_ST.write file_list_ uu____2009)
       in
    let uu____2019 =
      let uu____2021 = FStar_ST.read file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____2021
       in
    (res, uu____2019)
  
let file_list : Prims.unit -> Prims.string Prims.list =
  fun uu____2030  -> FStar_ST.read file_list_ 
let restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____2042 = specs ()  in
       FStar_Getopt.parse_cmdline uu____2042 (fun x  -> ())  in
     (let uu____2046 =
        let uu____2049 =
          let uu____2050 =
            FStar_List.map (fun _0_48  -> String _0_48) old_verify_module  in
          List uu____2050  in
        ("verify_module", uu____2049)  in
      set_option' uu____2046);
     r)
  
let should_verify : Prims.string -> Prims.bool =
  fun m  ->
    let uu____2055 = get_lax ()  in
    if uu____2055
    then false
    else
      (let uu____2057 = get_verify_all ()  in
       if uu____2057
       then true
       else
         (let uu____2059 = get_verify_module ()  in
          match uu____2059 with
          | [] ->
              let uu____2061 = file_list ()  in
              FStar_List.existsML
                (fun f  ->
                   let f1 = FStar_Util.basename f  in
                   let f2 =
                     let uu____2066 =
                       let uu____2067 =
                         let uu____2068 =
                           let uu____2069 = FStar_Util.get_file_extension f1
                              in
                           FStar_String.length uu____2069  in
                         (FStar_String.length f1) - uu____2068  in
                       uu____2067 - (Prims.parse_int "1")  in
                     FStar_String.substring f1 (Prims.parse_int "0")
                       uu____2066
                      in
                   (FStar_String.lowercase f2) = m) uu____2061
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
  
let dont_gen_projectors : Prims.string -> Prims.bool =
  fun m  ->
    let uu____2079 = get___temp_no_proj ()  in
    FStar_List.contains m uu____2079
  
let should_print_message : Prims.string -> Prims.bool =
  fun m  ->
    let uu____2084 = should_verify m  in
    if uu____2084 then m <> "Prims" else false
  
let include_path : Prims.unit -> Prims.string Prims.list =
  fun uu____2089  ->
    let uu____2090 = get_no_default_includes ()  in
    if uu____2090
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____2096 =
         let uu____2098 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____2098
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____2105 =
         let uu____2107 = get_include ()  in
         FStar_List.append uu____2107 ["."]  in
       FStar_List.append uu____2096 uu____2105)
  
let find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____2113 = FStar_Util.is_path_absolute filename  in
    if uu____2113
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____2118 =
         let uu____2120 = include_path ()  in FStar_List.rev uu____2120  in
       FStar_Util.find_map uu____2118
         (fun p  ->
            let path = FStar_Util.join_paths p filename  in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let prims : Prims.unit -> Prims.string =
  fun uu____2128  ->
    let uu____2129 = get_prims ()  in
    match uu____2129 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____2132 = find_file filename  in
        (match uu____2132 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____2135 =
               let uu____2136 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename
                  in
               FStar_Util.Failure uu____2136  in
             raise uu____2135)
    | FStar_Pervasives_Native.Some x -> x
  
let prims_basename : Prims.unit -> Prims.string =
  fun uu____2140  ->
    let uu____2141 = prims ()  in FStar_Util.basename uu____2141
  
let pervasives : Prims.unit -> Prims.string =
  fun uu____2144  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____2146 = find_file filename  in
    match uu____2146 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____2149 =
          let uu____2150 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename
             in
          FStar_Util.Failure uu____2150  in
        raise uu____2149
  
let pervasives_basename : Prims.unit -> Prims.string =
  fun uu____2153  ->
    let uu____2154 = pervasives ()  in FStar_Util.basename uu____2154
  
let pervasives_native_basename : Prims.unit -> Prims.string =
  fun uu____2157  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____2159 = find_file filename  in
    match uu____2159 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____2162 =
          let uu____2163 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename
             in
          FStar_Util.Failure uu____2163  in
        raise uu____2162
  
let prepend_output_dir : Prims.string -> Prims.string =
  fun fname  ->
    let uu____2167 = get_odir ()  in
    match uu____2167 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
  
let __temp_no_proj : Prims.string -> Prims.bool =
  fun s  ->
    let uu____2173 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____2173 (FStar_List.contains s)
  
let admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____2178  -> get_admit_smt_queries () 
let check_hints : Prims.unit -> Prims.bool =
  fun uu____2181  -> get_check_hints () 
let codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2185  -> get_codegen () 
let codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____2190  ->
    let uu____2191 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____2191
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let debug_any : Prims.unit -> Prims.bool =
  fun uu____2200  -> let uu____2201 = get_debug ()  in uu____2201 <> [] 
let debug_at_level : Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      ((modul = "") ||
         (let uu____2210 = get_debug ()  in
          FStar_All.pipe_right uu____2210 (FStar_List.contains modul)))
        && (debug_level_geq level)
  
let dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2216  -> get_dep () 
let detail_errors : Prims.unit -> Prims.bool =
  fun uu____2219  -> get_detail_errors () 
let doc : Prims.unit -> Prims.bool = fun uu____2222  -> get_doc () 
let dump_module : Prims.string -> Prims.bool =
  fun s  ->
    let uu____2226 = get_dump_module ()  in
    FStar_All.pipe_right uu____2226 (FStar_List.contains s)
  
let eager_inference : Prims.unit -> Prims.bool =
  fun uu____2231  -> get_eager_inference () 
let explicit_deps : Prims.unit -> Prims.bool =
  fun uu____2234  -> get_explicit_deps () 
let extract_all : Prims.unit -> Prims.bool =
  fun uu____2237  -> get_extract_all () 
let fs_typ_app : Prims.string -> Prims.bool =
  fun filename  ->
    let uu____2241 = FStar_ST.read light_off_files  in
    FStar_List.contains filename uu____2241
  
let full_context_dependency : Prims.unit -> Prims.bool =
  fun uu____2248  -> true 
let hide_genident_nums : Prims.unit -> Prims.bool =
  fun uu____2251  -> get_hide_genident_nums () 
let hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____2254  -> get_hide_uvar_nums () 
let hint_info : Prims.unit -> Prims.bool =
  fun uu____2257  -> get_hint_info () 
let hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2261  -> get_hint_file () 
let ide : Prims.unit -> Prims.bool = fun uu____2264  -> get_ide () 
let indent : Prims.unit -> Prims.bool = fun uu____2267  -> get_indent () 
let initial_fuel : Prims.unit -> Prims.int =
  fun uu____2270  ->
    let uu____2271 = get_initial_fuel ()  in
    let uu____2272 = get_max_fuel ()  in Prims.min uu____2271 uu____2272
  
let initial_ifuel : Prims.unit -> Prims.int =
  fun uu____2275  ->
    let uu____2276 = get_initial_ifuel ()  in
    let uu____2277 = get_max_ifuel ()  in Prims.min uu____2276 uu____2277
  
let interactive : Prims.unit -> Prims.bool =
  fun uu____2280  -> (get_in ()) || (get_ide ()) 
let lax : Prims.unit -> Prims.bool = fun uu____2283  -> get_lax () 
let lax_except : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2287  -> get_lax_except () 
let legacy_interactive : Prims.unit -> Prims.bool =
  fun uu____2290  -> get_in () 
let log_queries : Prims.unit -> Prims.bool =
  fun uu____2293  -> get_log_queries () 
let log_types : Prims.unit -> Prims.bool =
  fun uu____2296  -> get_log_types () 
let max_fuel : Prims.unit -> Prims.int = fun uu____2299  -> get_max_fuel () 
let max_ifuel : Prims.unit -> Prims.int = fun uu____2302  -> get_max_ifuel () 
let min_fuel : Prims.unit -> Prims.int = fun uu____2305  -> get_min_fuel () 
let ml_ish : Prims.unit -> Prims.bool = fun uu____2308  -> get_MLish () 
let set_ml_ish : Prims.unit -> Prims.unit =
  fun uu____2311  -> set_option "MLish" (Bool true) 
let n_cores : Prims.unit -> Prims.int = fun uu____2314  -> get_n_cores () 
let no_default_includes : Prims.unit -> Prims.bool =
  fun uu____2317  -> get_no_default_includes () 
let no_extract : Prims.string -> Prims.bool =
  fun s  ->
    let uu____2321 = get_no_extract ()  in
    FStar_All.pipe_right uu____2321 (FStar_List.contains s)
  
let no_location_info : Prims.unit -> Prims.bool =
  fun uu____2326  -> get_no_location_info () 
let output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2330  -> get_odir () 
let ugly : Prims.unit -> Prims.bool = fun uu____2333  -> get_ugly () 
let print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____2336  -> get_print_bound_var_types () 
let print_effect_args : Prims.unit -> Prims.bool =
  fun uu____2339  -> get_print_effect_args () 
let print_fuels : Prims.unit -> Prims.bool =
  fun uu____2342  -> get_print_fuels () 
let print_implicits : Prims.unit -> Prims.bool =
  fun uu____2345  -> get_print_implicits () 
let print_real_names : Prims.unit -> Prims.bool =
  fun uu____2348  -> (get_prn ()) || (get_print_full_names ()) 
let print_universes : Prims.unit -> Prims.bool =
  fun uu____2351  -> get_print_universes () 
let print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____2354  -> get_print_z3_statistics () 
let record_hints : Prims.unit -> Prims.bool =
  fun uu____2357  -> get_record_hints () 
let reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2361  -> get_reuse_hint_for () 
let silent : Prims.unit -> Prims.bool = fun uu____2364  -> get_silent () 
let smtencoding_elim_box : Prims.unit -> Prims.bool =
  fun uu____2367  -> get_smtencoding_elim_box () 
let smtencoding_nl_arith_native : Prims.unit -> Prims.bool =
  fun uu____2370  ->
    let uu____2371 = get_smtencoding_nl_arith_repr ()  in
    uu____2371 = "native"
  
let smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool =
  fun uu____2374  ->
    let uu____2375 = get_smtencoding_nl_arith_repr ()  in
    uu____2375 = "wrapped"
  
let smtencoding_nl_arith_default : Prims.unit -> Prims.bool =
  fun uu____2378  ->
    let uu____2379 = get_smtencoding_nl_arith_repr ()  in
    uu____2379 = "boxwrap"
  
let smtencoding_l_arith_native : Prims.unit -> Prims.bool =
  fun uu____2382  ->
    let uu____2383 = get_smtencoding_l_arith_repr ()  in
    uu____2383 = "native"
  
let smtencoding_l_arith_default : Prims.unit -> Prims.bool =
  fun uu____2386  ->
    let uu____2387 = get_smtencoding_l_arith_repr ()  in
    uu____2387 = "boxwrap"
  
let split_cases : Prims.unit -> Prims.int =
  fun uu____2390  -> get_split_cases () 
let timing : Prims.unit -> Prims.bool = fun uu____2393  -> get_timing () 
let trace_error : Prims.unit -> Prims.bool =
  fun uu____2396  -> get_trace_error () 
let unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____2399  -> get_unthrottle_inductives () 
let use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____2402  -> get_use_eq_at_higher_order () 
let use_hints : Prims.unit -> Prims.bool =
  fun uu____2405  -> get_use_hints () 
let use_tactics : Prims.unit -> Prims.bool =
  fun uu____2408  -> get_use_tactics () 
let using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____2413  -> get_using_facts_from () 
let verify_all : Prims.unit -> Prims.bool =
  fun uu____2416  -> get_verify_all () 
let verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____2420  -> get_verify_module () 
let warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____2423  -> get_warn_default_effects () 
let z3_exe : Prims.unit -> Prims.string =
  fun uu____2426  ->
    let uu____2427 = get_smt ()  in
    match uu____2427 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let z3_cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____2433  -> get_z3cliopt () 
let z3_refresh : Prims.unit -> Prims.bool =
  fun uu____2436  -> get_z3refresh () 
let z3_rlimit : Prims.unit -> Prims.int = fun uu____2439  -> get_z3rlimit () 
let z3_rlimit_factor : Prims.unit -> Prims.int =
  fun uu____2442  -> get_z3rlimit_factor () 
let z3_seed : Prims.unit -> Prims.int = fun uu____2445  -> get_z3seed () 
let z3_timeout : Prims.unit -> Prims.int =
  fun uu____2448  -> get_z3timeout () 
let no_positivity : Prims.unit -> Prims.bool =
  fun uu____2451  -> get_no_positivity () 
let should_extract : Prims.string -> Prims.bool =
  fun m  ->
    (let uu____2455 = no_extract m  in Prims.op_Negation uu____2455) &&
      ((extract_all ()) ||
         (let uu____2456 = get_extract_module ()  in
          match uu____2456 with
          | [] ->
              let uu____2458 = get_extract_namespace ()  in
              (match uu____2458 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
  