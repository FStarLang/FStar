open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let uu___is_Low : debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____7 -> false 
let uu___is_Medium : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____11 -> false
  
let uu___is_High : debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____15 -> false 
let uu___is_Extreme : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____19 -> false
  
let uu___is_Other : debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____24 -> false
  
let __proj__Other__item___0 : debug_level_t -> Prims.string =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let uu___is_Bool : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____49 -> false
  
let __proj__Bool__item___0 : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let uu___is_String : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____61 -> false
  
let __proj__String__item___0 : option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0 
let uu___is_Int : option_val -> Prims.bool =
  fun projectee  -> match projectee with | Int _0 -> true | uu____73 -> false 
let __proj__Int__item___0 : option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0 
let uu___is_List : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____86 -> false
  
let __proj__List__item___0 : option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0 
let uu___is_Unset : option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____100 -> false
  
type options =
  | Set 
  | Reset 
  | Restore 
let uu___is_Set : options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____104 -> false 
let uu___is_Reset : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____108 -> false
  
let uu___is_Restore : options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____112 -> false
  
let __unit_tests__ : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let __unit_tests : Prims.unit -> Prims.bool =
  fun uu____118  -> FStar_ST.read __unit_tests__ 
let __set_unit_tests : Prims.unit -> Prims.unit =
  fun uu____123  -> FStar_ST.write __unit_tests__ true 
let __clear_unit_tests : Prims.unit -> Prims.unit =
  fun uu____128  -> FStar_ST.write __unit_tests__ false 
let as_bool : option_val -> Prims.bool =
  fun uu___47_133  ->
    match uu___47_133 with
    | Bool b -> b
    | uu____135 -> failwith "Impos: expected Bool"
  
let as_int : option_val -> Prims.int =
  fun uu___48_138  ->
    match uu___48_138 with
    | Int b -> b
    | uu____140 -> failwith "Impos: expected Int"
  
let as_string : option_val -> Prims.string =
  fun uu___49_143  ->
    match uu___49_143 with
    | String b -> b
    | uu____145 -> failwith "Impos: expected String"
  
let as_list as_t uu___50_161 =
  match uu___50_161 with
  | List ts -> FStar_All.pipe_right ts (FStar_List.map as_t)
  | uu____168 -> failwith "Impos: expected List" 
let as_option as_t uu___51_185 =
  match uu___51_185 with
  | Unset  -> None
  | v1 -> let uu____189 = as_t v1  in Some uu____189 
let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let peek : Prims.unit -> option_val FStar_Util.smap =
  fun uu____201  ->
    let uu____202 = FStar_ST.read fstar_options  in FStar_List.hd uu____202
  
let pop : Prims.unit -> Prims.unit =
  fun uu____212  ->
    let uu____213 = FStar_ST.read fstar_options  in
    match uu____213 with
    | []|_::[] -> failwith "TOO MANY POPS!"
    | uu____224::tl1 -> FStar_ST.write fstar_options tl1
  
let push : Prims.unit -> Prims.unit =
  fun uu____236  ->
    let uu____237 =
      let uu____240 =
        let uu____242 = peek ()  in FStar_Util.smap_copy uu____242  in
      let uu____244 = FStar_ST.read fstar_options  in uu____240 :: uu____244
       in
    FStar_ST.write fstar_options uu____237
  
let set_option : Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____262 = peek ()  in FStar_Util.smap_add uu____262 k v1
  
let set_option' : (Prims.string * option_val) -> Prims.unit =
  fun uu____268  -> match uu____268 with | (k,v1) -> set_option k v1 
let light_off_files : Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let add_light_off_file : Prims.string -> Prims.unit =
  fun filename  ->
    let uu____281 =
      let uu____283 = FStar_ST.read light_off_files  in filename :: uu____283
       in
    FStar_ST.write light_off_files uu____281
  
let init : Prims.unit -> Prims.unit =
  fun uu____293  ->
    let vals =
      [("__temp_no_proj", (List []));
      ("_fstar_home", (String ""));
      ("_include_path", (List []));
      ("admit_smt_queries", (Bool false));
      ("cardinality", (String "off"));
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
      ("fsi", (Bool false));
      ("fstar_home", Unset);
      ("full_context_dependency", (Bool true));
      ("hide_genident_nums", (Bool false));
      ("hide_uvar_nums", (Bool false));
      ("hint_info", (Bool false));
      ("in", (Bool false));
      ("include", (List []));
      ("indent", (Bool false));
      ("initial_fuel", (Int (Prims.parse_int "2")));
      ("initial_ifuel", (Int (Prims.parse_int "1")));
      ("inline_arith", (Bool false));
      ("lax", (Bool false));
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
      ("no_warn_top_level_effects", (Bool true));
      ("odir", Unset);
      ("prims", Unset);
      ("pretype", (Bool true));
      ("prims_ref", Unset);
      ("print_before_norm", (Bool false));
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
      ("split_cases", (Int (Prims.parse_int "0")));
      ("timing", (Bool false));
      ("trace_error", (Bool false));
      ("unthrottle_inductives", (Bool false));
      ("use_eq_at_higher_order", (Bool false));
      ("use_hints", (Bool false));
      ("use_tactics", (Bool false));
      ("verify", (Bool true));
      ("verify_all", (Bool false));
      ("verify_module", (List []));
      ("warn_default_effects", (Bool false));
      ("z3refresh", (Bool false));
      ("z3rlimit", (Int (Prims.parse_int "5")));
      ("z3seed", (Int (Prims.parse_int "0")));
      ("z3timeout", (Int (Prims.parse_int "5")));
      ("z3cliopt", (List []));
      ("__no_positivity", (Bool false))]  in
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right vals (FStar_List.iter set_option')
  
let clear : Prims.unit -> Prims.unit =
  fun uu____466  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.write fstar_options [o];
    FStar_ST.write light_off_files [];
    init ()
  
let _run : Prims.unit = clear () 
let lookup_opt s c =
  let uu____497 =
    let uu____499 = peek ()  in FStar_Util.smap_try_find uu____499 s  in
  match uu____497 with
  | None  ->
      failwith
        (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
  | Some s1 -> c s1 
let get_admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____504  -> lookup_opt "admit_smt_queries" as_bool 
let get_cardinality : Prims.unit -> Prims.string =
  fun uu____507  -> lookup_opt "cardinality" as_string 
let get_codegen : Prims.unit -> Prims.string Prims.option =
  fun uu____511  -> lookup_opt "codegen" (as_option as_string) 
let get_codegen_lib : Prims.unit -> Prims.string Prims.list =
  fun uu____516  -> lookup_opt "codegen-lib" (as_list as_string) 
let get_debug : Prims.unit -> Prims.string Prims.list =
  fun uu____521  -> lookup_opt "debug" (as_list as_string) 
let get_debug_level : Prims.unit -> Prims.string Prims.list =
  fun uu____526  -> lookup_opt "debug_level" (as_list as_string) 
let get_dep : Prims.unit -> Prims.string Prims.option =
  fun uu____531  -> lookup_opt "dep" (as_option as_string) 
let get_detail_errors : Prims.unit -> Prims.bool =
  fun uu____535  -> lookup_opt "detail_errors" as_bool 
let get_doc : Prims.unit -> Prims.bool =
  fun uu____538  -> lookup_opt "doc" as_bool 
let get_dump_module : Prims.unit -> Prims.string Prims.list =
  fun uu____542  -> lookup_opt "dump_module" (as_list as_string) 
let get_eager_inference : Prims.unit -> Prims.bool =
  fun uu____546  -> lookup_opt "eager_inference" as_bool 
let get_explicit_deps : Prims.unit -> Prims.bool =
  fun uu____549  -> lookup_opt "explicit_deps" as_bool 
let get_extract_all : Prims.unit -> Prims.bool =
  fun uu____552  -> lookup_opt "extract_all" as_bool 
let get_extract_module : Prims.unit -> Prims.string Prims.list =
  fun uu____556  -> lookup_opt "extract_module" (as_list as_string) 
let get_extract_namespace : Prims.unit -> Prims.string Prims.list =
  fun uu____561  -> lookup_opt "extract_namespace" (as_list as_string) 
let get_fs_typ_app : Prims.unit -> Prims.bool =
  fun uu____565  -> lookup_opt "fs_typ_app" as_bool 
let get_fstar_home : Prims.unit -> Prims.string Prims.option =
  fun uu____569  -> lookup_opt "fstar_home" (as_option as_string) 
let get_hide_genident_nums : Prims.unit -> Prims.bool =
  fun uu____573  -> lookup_opt "hide_genident_nums" as_bool 
let get_hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____576  -> lookup_opt "hide_uvar_nums" as_bool 
let get_hint_info : Prims.unit -> Prims.bool =
  fun uu____579  -> lookup_opt "hint_info" as_bool 
let get_in : Prims.unit -> Prims.bool =
  fun uu____582  -> lookup_opt "in" as_bool 
let get_include : Prims.unit -> Prims.string Prims.list =
  fun uu____586  -> lookup_opt "include" (as_list as_string) 
let get_indent : Prims.unit -> Prims.bool =
  fun uu____590  -> lookup_opt "indent" as_bool 
let get_initial_fuel : Prims.unit -> Prims.int =
  fun uu____593  -> lookup_opt "initial_fuel" as_int 
let get_initial_ifuel : Prims.unit -> Prims.int =
  fun uu____596  -> lookup_opt "initial_ifuel" as_int 
let get_inline_arith : Prims.unit -> Prims.bool =
  fun uu____599  -> lookup_opt "inline_arith" as_bool 
let get_lax : Prims.unit -> Prims.bool =
  fun uu____602  -> lookup_opt "lax" as_bool 
let get_log_queries : Prims.unit -> Prims.bool =
  fun uu____605  -> lookup_opt "log_queries" as_bool 
let get_log_types : Prims.unit -> Prims.bool =
  fun uu____608  -> lookup_opt "log_types" as_bool 
let get_max_fuel : Prims.unit -> Prims.int =
  fun uu____611  -> lookup_opt "max_fuel" as_int 
let get_max_ifuel : Prims.unit -> Prims.int =
  fun uu____614  -> lookup_opt "max_ifuel" as_int 
let get_min_fuel : Prims.unit -> Prims.int =
  fun uu____617  -> lookup_opt "min_fuel" as_int 
let get_MLish : Prims.unit -> Prims.bool =
  fun uu____620  -> lookup_opt "MLish" as_bool 
let get_n_cores : Prims.unit -> Prims.int =
  fun uu____623  -> lookup_opt "n_cores" as_int 
let get_no_default_includes : Prims.unit -> Prims.bool =
  fun uu____626  -> lookup_opt "no_default_includes" as_bool 
let get_no_extract : Prims.unit -> Prims.string Prims.list =
  fun uu____630  -> lookup_opt "no_extract" (as_list as_string) 
let get_no_location_info : Prims.unit -> Prims.bool =
  fun uu____634  -> lookup_opt "no_location_info" as_bool 
let get_warn_top_level_effects : Prims.unit -> Prims.bool =
  fun uu____637  -> lookup_opt "no_warn_top_level_effects" as_bool 
let get_odir : Prims.unit -> Prims.string Prims.option =
  fun uu____641  -> lookup_opt "odir" (as_option as_string) 
let get_prims : Prims.unit -> Prims.string Prims.option =
  fun uu____646  -> lookup_opt "prims" (as_option as_string) 
let get_print_before_norm : Prims.unit -> Prims.bool =
  fun uu____650  -> lookup_opt "print_before_norm" as_bool 
let get_print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____653  -> lookup_opt "print_bound_var_types" as_bool 
let get_print_effect_args : Prims.unit -> Prims.bool =
  fun uu____656  -> lookup_opt "print_effect_args" as_bool 
let get_print_fuels : Prims.unit -> Prims.bool =
  fun uu____659  -> lookup_opt "print_fuels" as_bool 
let get_print_full_names : Prims.unit -> Prims.bool =
  fun uu____662  -> lookup_opt "print_full_names" as_bool 
let get_print_implicits : Prims.unit -> Prims.bool =
  fun uu____665  -> lookup_opt "print_implicits" as_bool 
let get_print_universes : Prims.unit -> Prims.bool =
  fun uu____668  -> lookup_opt "print_universes" as_bool 
let get_print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____671  -> lookup_opt "print_z3_statistics" as_bool 
let get_prn : Prims.unit -> Prims.bool =
  fun uu____674  -> lookup_opt "prn" as_bool 
let get_record_hints : Prims.unit -> Prims.bool =
  fun uu____677  -> lookup_opt "record_hints" as_bool 
let get_reuse_hint_for : Prims.unit -> Prims.string Prims.option =
  fun uu____681  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let get_show_signatures : Prims.unit -> Prims.string Prims.list =
  fun uu____686  -> lookup_opt "show_signatures" (as_list as_string) 
let get_silent : Prims.unit -> Prims.bool =
  fun uu____690  -> lookup_opt "silent" as_bool 
let get_smt : Prims.unit -> Prims.string Prims.option =
  fun uu____694  -> lookup_opt "smt" (as_option as_string) 
let get_split_cases : Prims.unit -> Prims.int =
  fun uu____698  -> lookup_opt "split_cases" as_int 
let get_timing : Prims.unit -> Prims.bool =
  fun uu____701  -> lookup_opt "timing" as_bool 
let get_trace_error : Prims.unit -> Prims.bool =
  fun uu____704  -> lookup_opt "trace_error" as_bool 
let get_unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____707  -> lookup_opt "unthrottle_inductives" as_bool 
let get_use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____710  -> lookup_opt "use_eq_at_higher_order" as_bool 
let get_use_hints : Prims.unit -> Prims.bool =
  fun uu____713  -> lookup_opt "use_hints" as_bool 
let get_use_tactics : Prims.unit -> Prims.bool =
  fun uu____716  -> lookup_opt "use_tactics" as_bool 
let get_verify_all : Prims.unit -> Prims.bool =
  fun uu____719  -> lookup_opt "verify_all" as_bool 
let get_verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____723  -> lookup_opt "verify_module" (as_list as_string) 
let get___temp_no_proj : Prims.unit -> Prims.string Prims.list =
  fun uu____728  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let get_version : Prims.unit -> Prims.bool =
  fun uu____732  -> lookup_opt "version" as_bool 
let get_warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____735  -> lookup_opt "warn_default_effects" as_bool 
let get_z3cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____739  -> lookup_opt "z3cliopt" (as_list as_string) 
let get_z3refresh : Prims.unit -> Prims.bool =
  fun uu____743  -> lookup_opt "z3refresh" as_bool 
let get_z3rlimit : Prims.unit -> Prims.int =
  fun uu____746  -> lookup_opt "z3rlimit" as_int 
let get_z3seed : Prims.unit -> Prims.int =
  fun uu____749  -> lookup_opt "z3seed" as_int 
let get_z3timeout : Prims.unit -> Prims.int =
  fun uu____752  -> lookup_opt "z3timeout" as_int 
let get_no_positivity : Prims.unit -> Prims.bool =
  fun uu____755  -> lookup_opt "__no_positivity" as_bool 
let dlevel : Prims.string -> debug_level_t =
  fun uu___52_758  ->
    match uu___52_758 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other _|Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let debug_level_geq : debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____770 = get_debug_level ()  in
    FStar_All.pipe_right uu____770
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let include_path_base_dirs : Prims.string Prims.list = ["/lib"; "/lib/fstar"] 
let universe_include_path_base_dirs : Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"] 
let _version : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _platform : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _compiler : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _date : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let _commit : Prims.string FStar_ST.ref = FStar_Util.mk_ref "" 
let display_version : Prims.unit -> Prims.unit =
  fun uu____798  ->
    let uu____799 =
      let uu____800 = FStar_ST.read _version  in
      let uu____803 = FStar_ST.read _platform  in
      let uu____806 = FStar_ST.read _compiler  in
      let uu____809 = FStar_ST.read _date  in
      let uu____812 = FStar_ST.read _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____800
        uu____803 uu____806 uu____809 uu____812
       in
    FStar_Util.print_string uu____799
  
let display_usage_aux specs =
  FStar_Util.print_string "fstar.exe [options] file[s]\n";
  FStar_List.iter
    (fun uu____842  ->
       match uu____842 with
       | (uu____848,flag,p,doc) ->
           (match p with
            | FStar_Getopt.ZeroArgs ig ->
                if doc = ""
                then
                  let uu____857 =
                    let uu____858 = FStar_Util.colorize_bold flag  in
                    FStar_Util.format1 "  --%s\n" uu____858  in
                  FStar_Util.print_string uu____857
                else
                  (let uu____860 =
                     let uu____861 = FStar_Util.colorize_bold flag  in
                     FStar_Util.format2 "  --%s  %s\n" uu____861 doc  in
                   FStar_Util.print_string uu____860)
            | FStar_Getopt.OneArg (uu____862,argname) ->
                if doc = ""
                then
                  let uu____868 =
                    let uu____869 = FStar_Util.colorize_bold flag  in
                    let uu____870 = FStar_Util.colorize_bold argname  in
                    FStar_Util.format2 "  --%s %s\n" uu____869 uu____870  in
                  FStar_Util.print_string uu____868
                else
                  (let uu____872 =
                     let uu____873 = FStar_Util.colorize_bold flag  in
                     let uu____874 = FStar_Util.colorize_bold argname  in
                     FStar_Util.format3 "  --%s %s  %s\n" uu____873 uu____874
                       doc
                      in
                   FStar_Util.print_string uu____872))) specs
  
let mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____888 = o  in
    match uu____888 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____909 =
                let uu____910 = let uu____913 = f ()  in (name, uu____913)
                   in
                set_option' uu____910  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x =
                let uu____924 = let uu____927 = f x  in (name, uu____927)  in
                set_option' uu____924  in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let cons_extract_module : Prims.string -> option_val =
  fun s  ->
    let uu____934 =
      let uu____936 =
        let uu____938 = get_extract_module ()  in (FStar_String.lowercase s)
          :: uu____938
         in
      FStar_All.pipe_right uu____936
        (FStar_List.map (fun _0_25  -> String _0_25))
       in
    List uu____934
  
let cons_extract_namespace : Prims.string -> option_val =
  fun s  ->
    let uu____945 =
      let uu____947 =
        let uu____949 = get_extract_namespace ()  in
        (FStar_String.lowercase s) :: uu____949  in
      FStar_All.pipe_right uu____947
        (FStar_List.map (fun _0_26  -> String _0_26))
       in
    List uu____945
  
let add_extract_module : Prims.string -> Prims.unit =
  fun s  ->
    let uu____956 = cons_extract_module s  in
    set_option "extract_module" uu____956
  
let add_extract_namespace : Prims.string -> Prims.unit =
  fun s  ->
    let uu____960 = cons_extract_namespace s  in
    set_option "extract_namespace" uu____960
  
let cons_verify_module : Prims.string -> option_val =
  fun s  ->
    let uu____964 =
      let uu____966 =
        let uu____968 = get_verify_module ()  in (FStar_String.lowercase s)
          :: uu____968
         in
      FStar_All.pipe_right uu____966
        (FStar_List.map (fun _0_27  -> String _0_27))
       in
    List uu____964
  
let add_verify_module : Prims.string -> Prims.unit =
  fun s  ->
    let uu____975 = cons_verify_module s  in
    set_option "verify_module" uu____975
  
let rec specs :
  Prims.unit ->
    (FStar_Char.char * Prims.string * Prims.unit FStar_Getopt.opt_variant *
      Prims.string) Prims.list
  =
  fun uu____983  ->
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
      (FStar_Getopt.noshort, "cardinality",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1012 = validate_cardinality x  in String uu____1012)),
             "[off|warn|check]")),
        "Check cardinality constraints on inductive data types (default 'off')");
      (FStar_Getopt.noshort, "codegen",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1022 = parse_codegen s  in String uu____1022)),
             "[OCaml|FSharp|Kremlin]")), "Generate code for execution");
      (FStar_Getopt.noshort, "codegen-lib",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1032 =
                  let uu____1034 =
                    let uu____1036 = get_codegen_lib ()  in s :: uu____1036
                     in
                  FStar_All.pipe_right uu____1034
                    (FStar_List.map (fun _0_28  -> String _0_28))
                   in
                List uu____1032)), "[namespace]")),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
      (FStar_Getopt.noshort, "debug",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1049 =
                  let uu____1051 =
                    let uu____1053 = get_debug ()  in x :: uu____1053  in
                  FStar_All.pipe_right uu____1051
                    (FStar_List.map (fun _0_29  -> String _0_29))
                   in
                List uu____1049)), "[module name]")),
        "Print lots of debugging information while checking module");
      (FStar_Getopt.noshort, "debug_level",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1066 =
                  let uu____1068 =
                    let uu____1070 = get_debug_level ()  in x :: uu____1070
                     in
                  FStar_All.pipe_right uu____1068
                    (FStar_List.map (fun _0_30  -> String _0_30))
                   in
                List uu____1066)), "[Low|Medium|High|Extreme|...]")),
        "Control the verbosity of debugging info");
      (FStar_Getopt.noshort, "dep",
        (FStar_Getopt.OneArg
           (((fun x  ->
                if (x = "make") || (x = "graph")
                then String x
                else failwith "invalid argument to 'dep'")), "[make|graph]")),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");
      (FStar_Getopt.noshort, "detail_errors",
        (FStar_Getopt.ZeroArgs ((fun uu____1090  -> Bool true))),
        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "doc",
        (FStar_Getopt.ZeroArgs ((fun uu____1097  -> Bool true))),
        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");
      (FStar_Getopt.noshort, "dump_module",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1107 =
                  let uu____1109 =
                    let uu____1111 = get_dump_module ()  in x :: uu____1111
                     in
                  FStar_All.pipe_right uu____1109
                    (FStar_List.map (fun _0_31  -> String _0_31))
                   in
                FStar_All.pipe_right uu____1107 (fun _0_32  -> List _0_32))),
             "[module name]")), "");
      (FStar_Getopt.noshort, "eager_inference",
        (FStar_Getopt.ZeroArgs ((fun uu____1122  -> Bool true))),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
      (FStar_Getopt.noshort, "explicit_deps",
        (FStar_Getopt.ZeroArgs ((fun uu____1129  -> Bool true))),
        "Do not find dependencies automatically, the user provides them on the command-line");
      (FStar_Getopt.noshort, "extract_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1136  -> Bool true))),
        "Discover the complete dependency graph and do not stop at interface boundaries");
      (FStar_Getopt.noshort, "extract_module",
        (FStar_Getopt.OneArg (cons_extract_module, "[module name]")),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");
      (FStar_Getopt.noshort, "extract_namespace",
        (FStar_Getopt.OneArg (cons_extract_namespace, "[namespace name]")),
        "Only extract modules in the specified namespace");
      (FStar_Getopt.noshort, "fstar_home",
        (FStar_Getopt.OneArg (((fun _0_33  -> String _0_33)), "[dir]")),
        "Set the FSTAR_HOME variable to [dir]");
      (FStar_Getopt.noshort, "hide_genident_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1167  -> Bool true))),
        "Don't print generated identifier numbers");
      (FStar_Getopt.noshort, "hide_uvar_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1174  -> Bool true))),
        "Don't print unification variable numbers");
      (FStar_Getopt.noshort, "hint_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1181  -> Bool true))),
        "Print information regarding hints");
      (FStar_Getopt.noshort, "in",
        (FStar_Getopt.ZeroArgs ((fun uu____1188  -> Bool true))),
        "Interactive mode; reads input from stdin");
      (FStar_Getopt.noshort, "include",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1198 =
                  let uu____1200 =
                    let uu____1202 = get_include ()  in
                    FStar_List.append uu____1202 [s]  in
                  FStar_All.pipe_right uu____1200
                    (FStar_List.map (fun _0_34  -> String _0_34))
                   in
                List uu____1198)), "[path]")),
        "A directory in which to search for files included on the command line");
      (FStar_Getopt.noshort, "indent",
        (FStar_Getopt.ZeroArgs ((fun uu____1212  -> Bool true))),
        "Parses and outputs the files on the command line");
      (FStar_Getopt.noshort, "initial_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1222 = FStar_Util.int_of_string x  in
                Int uu____1222)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try initially (default 2)");
      (FStar_Getopt.noshort, "initial_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1232 = FStar_Util.int_of_string x  in
                Int uu____1232)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at first (default 1)");
      (FStar_Getopt.noshort, "inline_arith",
        (FStar_Getopt.ZeroArgs ((fun uu____1239  -> Bool true))),
        "Inline definitions of arithmetic functions in the SMT encoding");
      (FStar_Getopt.noshort, "lax",
        (FStar_Getopt.ZeroArgs ((fun uu____1246  -> Bool true))),
        "Run the lax-type checker only (admit all verification conditions)");
      (FStar_Getopt.noshort, "log_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1253  -> Bool true))),
        "Print types computed for data/val/let-bindings");
      (FStar_Getopt.noshort, "log_queries",
        (FStar_Getopt.ZeroArgs ((fun uu____1260  -> Bool true))),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");
      (FStar_Getopt.noshort, "max_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1270 = FStar_Util.int_of_string x  in
                Int uu____1270)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try at most (default 8)");
      (FStar_Getopt.noshort, "max_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1280 = FStar_Util.int_of_string x  in
                Int uu____1280)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at most (default 2)");
      (FStar_Getopt.noshort, "min_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1290 = FStar_Util.int_of_string x  in
                Int uu____1290)), "[non-negative integer]")),
        "Minimum number of unrolling of recursive functions to try (default 1)");
      (FStar_Getopt.noshort, "MLish",
        (FStar_Getopt.ZeroArgs ((fun uu____1297  -> Bool true))),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
      (FStar_Getopt.noshort, "n_cores",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1307 = FStar_Util.int_of_string x  in
                Int uu____1307)), "[positive integer]")),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");
      (FStar_Getopt.noshort, "no_default_includes",
        (FStar_Getopt.ZeroArgs ((fun uu____1314  -> Bool true))),
        "Ignore the default module search paths");
      (FStar_Getopt.noshort, "no_extract",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1324 =
                  let uu____1326 =
                    let uu____1328 = get_no_extract ()  in x :: uu____1328
                     in
                  FStar_All.pipe_right uu____1326
                    (FStar_List.map (fun _0_35  -> String _0_35))
                   in
                List uu____1324)), "[module name]")),
        "Do not extract code from this module");
      (FStar_Getopt.noshort, "no_location_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1338  -> Bool true))),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
      (FStar_Getopt.noshort, "odir",
        (FStar_Getopt.OneArg (((fun _0_36  -> String _0_36)), "[dir]")),
        "Place output in directory [dir]");
      (FStar_Getopt.noshort, "prims",
        (FStar_Getopt.OneArg (((fun _0_37  -> String _0_37)), "file")), "");
      (FStar_Getopt.noshort, "print_before_norm",
        (FStar_Getopt.ZeroArgs ((fun uu____1361  -> Bool true))),
        "Do not normalize types before printing (for debugging)");
      (FStar_Getopt.noshort, "print_bound_var_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1368  -> Bool true))),
        "Print the types of bound variables");
      (FStar_Getopt.noshort, "print_effect_args",
        (FStar_Getopt.ZeroArgs ((fun uu____1375  -> Bool true))),
        "Print inferred predicate transformers for all computation types");
      (FStar_Getopt.noshort, "print_fuels",
        (FStar_Getopt.ZeroArgs ((fun uu____1382  -> Bool true))),
        "Print the fuel amounts used for each successful query");
      (FStar_Getopt.noshort, "print_full_names",
        (FStar_Getopt.ZeroArgs ((fun uu____1389  -> Bool true))),
        "Print full names of variables");
      (FStar_Getopt.noshort, "print_implicits",
        (FStar_Getopt.ZeroArgs ((fun uu____1396  -> Bool true))),
        "Print implicit arguments");
      (FStar_Getopt.noshort, "print_universes",
        (FStar_Getopt.ZeroArgs ((fun uu____1403  -> Bool true))),
        "Print universes");
      (FStar_Getopt.noshort, "print_z3_statistics",
        (FStar_Getopt.ZeroArgs ((fun uu____1410  -> Bool true))),
        "Print Z3 statistics for each SMT query");
      (FStar_Getopt.noshort, "prn",
        (FStar_Getopt.ZeroArgs ((fun uu____1417  -> Bool true))),
        "Print full names (deprecated; use --print_full_names instead)");
      (FStar_Getopt.noshort, "record_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1424  -> Bool true))),
        "Record a database of hints for efficient proof replay");
      (FStar_Getopt.noshort, "reuse_hint_for",
        (FStar_Getopt.OneArg
           (((fun _0_38  -> String _0_38)),
             "top-level name in the current module")),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");
      (FStar_Getopt.noshort, "show_signatures",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1442 =
                  let uu____1444 =
                    let uu____1446 = get_show_signatures ()  in x ::
                      uu____1446
                     in
                  FStar_All.pipe_right uu____1444
                    (FStar_List.map (fun _0_39  -> String _0_39))
                   in
                List uu____1442)), "[module name]")),
        "Show the checked signatures for all top-level symbols in the module");
      (FStar_Getopt.noshort, "silent",
        (FStar_Getopt.ZeroArgs ((fun uu____1456  -> Bool true))), " ");
      (FStar_Getopt.noshort, "smt",
        (FStar_Getopt.OneArg (((fun _0_40  -> String _0_40)), "[path]")),
        "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)");
      (FStar_Getopt.noshort, "split_cases",
        (FStar_Getopt.OneArg
           (((fun n1  ->
                let uu____1474 = FStar_Util.int_of_string n1  in
                Int uu____1474)), "[positive integer]")),
        "Partition VC of a match into groups of [n] cases");
      (FStar_Getopt.noshort, "timing",
        (FStar_Getopt.ZeroArgs ((fun uu____1481  -> Bool true))),
        "Print the time it takes to verify each top-level definition");
      (FStar_Getopt.noshort, "trace_error",
        (FStar_Getopt.ZeroArgs ((fun uu____1488  -> Bool true))),
        "Don't print an error message; show an exception trace instead");
      (FStar_Getopt.noshort, "unthrottle_inductives",
        (FStar_Getopt.ZeroArgs ((fun uu____1495  -> Bool true))),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
      (FStar_Getopt.noshort, "use_eq_at_higher_order",
        (FStar_Getopt.ZeroArgs ((fun uu____1502  -> Bool true))),
        "Use equality constraints when comparing higher-order types (Temporary)");
      (FStar_Getopt.noshort, "use_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1509  -> Bool true))),
        "Use a previously recorded hints database for proof replay");
      (FStar_Getopt.noshort, "use_tactics",
        (FStar_Getopt.ZeroArgs ((fun uu____1516  -> Bool true))),
        "Pre-process a verification condition using a user-provided tactic (a flag to support migration to tactics gradually)");
      (FStar_Getopt.noshort, "verify_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1523  -> Bool true))),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");
      (FStar_Getopt.noshort, "verify_module",
        (FStar_Getopt.OneArg (cons_verify_module, "[module name]")),
        "Name of the module to verify");
      (FStar_Getopt.noshort, "__temp_no_proj",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1541 =
                  let uu____1543 =
                    let uu____1545 = get___temp_no_proj ()  in x ::
                      uu____1545
                     in
                  FStar_All.pipe_right uu____1543
                    (FStar_List.map (fun _0_41  -> String _0_41))
                   in
                List uu____1541)), "[module name]")),
        "Don't generate projectors for this module");
      ('v', "version",
        (FStar_Getopt.ZeroArgs
           ((fun uu____1555  ->
               display_version (); FStar_All.exit (Prims.parse_int "0")))),
        "Display version number");
      (FStar_Getopt.noshort, "warn_default_effects",
        (FStar_Getopt.ZeroArgs ((fun uu____1563  -> Bool true))),
        "Warn when (a -> b) is desugared to (a -> Tot b)");
      (FStar_Getopt.noshort, "z3cliopt",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1573 =
                  let uu____1575 =
                    let uu____1577 = get_z3cliopt ()  in
                    FStar_List.append uu____1577 [s]  in
                  FStar_All.pipe_right uu____1575
                    (FStar_List.map (fun _0_42  -> String _0_42))
                   in
                List uu____1573)), "[option]")), "Z3 command line options");
      (FStar_Getopt.noshort, "z3refresh",
        (FStar_Getopt.ZeroArgs ((fun uu____1587  -> Bool false))),
        "Restart Z3 after each query; useful for ensuring proof robustness");
      (FStar_Getopt.noshort, "z3rlimit",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1597 = FStar_Util.int_of_string s  in
                Int uu____1597)), "[positive integer]")),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
      (FStar_Getopt.noshort, "z3seed",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1607 = FStar_Util.int_of_string s  in
                Int uu____1607)), "[positive integer]")),
        "Set the Z3 random seed (default 0)");
      (FStar_Getopt.noshort, "z3timeout",
        (FStar_Getopt.OneArg
           (((fun s  ->
                FStar_Util.print_string
                  "Warning: z3timeout ignored; use z3rlimit instead\n";
                (let uu____1618 = FStar_Util.int_of_string s  in
                 Int uu____1618))), "[positive integer]")),
        "Set the Z3 per-query (soft) timeout to [t] seconds (default 5)");
      (FStar_Getopt.noshort, "__no_positivity",
        (FStar_Getopt.ZeroArgs ((fun uu____1625  -> Bool true))),
        "Don't check positivity of inductive types")]
       in
    let uu____1631 = FStar_List.map mk_spec specs1  in
    ('h', "help",
      (FStar_Getopt.ZeroArgs
         (fun x  ->
            display_usage_aux specs1; FStar_All.exit (Prims.parse_int "0"))),
      "Display this information") :: uu____1631

and parse_codegen : Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Kremlin"|"OCaml"|"FSharp" -> s
    | uu____1652 ->
        (FStar_Util.print_string "Wrong argument to codegen flag\n";
         (let uu____1655 = specs ()  in display_usage_aux uu____1655);
         FStar_All.exit (Prims.parse_int "1"))

and validate_cardinality : Prims.string -> Prims.string =
  fun x  ->
    match x with
    | "warn"|"check"|"off" -> x
    | uu____1663 ->
        (FStar_Util.print_string "Wrong argument to cardinality flag\n";
         (let uu____1666 = specs ()  in display_usage_aux uu____1666);
         FStar_All.exit (Prims.parse_int "1"))

let settable : Prims.string -> Prims.bool =
  fun uu___53_1675  ->
    match uu___53_1675 with
    | "admit_smt_queries"
      |"cardinality"
       |"debug"
        |"debug_level"
         |"detail_errors"
          |"eager_inference"
           |"hide_genident_nums"
            |"hide_uvar_nums"
             |"hint_info"
              |"initial_fuel"
               |"initial_ifuel"
                |"inline_arith"
                 |"lax"
                  |"log_types"
                   |"log_queries"
                    |"max_fuel"
                     |"max_ifuel"
                      |"min_fuel"
                       |"print_before_norm"
                        |"print_bound_var_types"
                         |"print_effect_args"
                          |"print_fuels"
                           |"print_full_names"
                            |"print_implicits"
                             |"print_universes"
                              |"print_z3_statistics"
                               |"prn"
                                |"show_signatures"
                                 |"silent"
                                  |"split_cases"
                                   |"timing"
                                    |"trace_error"
                                     |"unthrottle_inductives"
                                      |"use_eq_at_higher_order"
                                       |"use_tactics"
                                        |"__temp_no_proj"
                                         |"no_warn_top_level_effects"
                                          |"reuse_hint_for"|"z3refresh"
        -> true
    | uu____1676 -> false
  
let resettable : Prims.string -> Prims.bool =
  fun s  ->
    (((settable s) || (s = "z3timeout")) || (s = "z3rlimit")) ||
      (s = "z3seed")
  
let all_specs : FStar_Getopt.opt Prims.list = specs () 
let settable_specs :
  (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant
    * Prims.string) Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____1699  ->
          match uu____1699 with
          | (uu____1705,x,uu____1707,uu____1708) -> settable x))
  
let resettable_specs :
  (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant
    * Prims.string) Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____1729  ->
          match uu____1729 with
          | (uu____1735,x,uu____1737,uu____1738) -> resettable x))
  
let display_usage : Prims.unit -> Prims.unit =
  fun uu____1743  ->
    let uu____1744 = specs ()  in display_usage_aux uu____1744
  
let fstar_home : Prims.unit -> Prims.string =
  fun uu____1753  ->
    let uu____1754 = get_fstar_home ()  in
    match uu____1754 with
    | None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        (set_option' ("fstar_home", (String x1)); x1)
    | Some x -> x
  
let set_options : options -> Prims.string -> FStar_Getopt.parse_cmdline_res =
  fun o  ->
    fun s  ->
      let specs1 =
        match o with
        | Set  -> resettable_specs
        | Reset  -> resettable_specs
        | Restore  -> all_specs  in
      FStar_Getopt.parse_string specs1 (fun uu____1779  -> ()) s
  
let file_list_ : Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let parse_cmd_line :
  Prims.unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) =
  fun uu____1790  ->
    let res =
      let uu____1792 = specs ()  in
      FStar_Getopt.parse_cmdline uu____1792
        (fun i  ->
           let uu____1795 =
             let uu____1797 = FStar_ST.read file_list_  in
             FStar_List.append uu____1797 [i]  in
           FStar_ST.write file_list_ uu____1795)
       in
    let uu____1805 = FStar_ST.read file_list_  in (res, uu____1805)
  
let file_list : Prims.unit -> Prims.string Prims.list =
  fun uu____1814  -> FStar_ST.read file_list_ 
let restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____1826 = specs ()  in
       FStar_Getopt.parse_cmdline uu____1826 (fun x  -> ())  in
     (let uu____1830 =
        let uu____1833 =
          let uu____1834 =
            FStar_List.map (fun _0_43  -> String _0_43) old_verify_module  in
          List uu____1834  in
        ("verify_module", uu____1833)  in
      set_option' uu____1830);
     r)
  
let should_verify : Prims.string -> Prims.bool =
  fun m  ->
    let uu____1839 = get_lax ()  in
    if uu____1839
    then false
    else
      (let uu____1841 = get_verify_all ()  in
       if uu____1841
       then true
       else
         (let uu____1843 = get_verify_module ()  in
          match uu____1843 with
          | [] ->
              let uu____1845 = file_list ()  in
              FStar_List.existsML
                (fun f  ->
                   let f1 = FStar_Util.basename f  in
                   let f2 =
                     let uu____1850 =
                       let uu____1851 =
                         let uu____1852 =
                           let uu____1853 = FStar_Util.get_file_extension f1
                              in
                           FStar_String.length uu____1853  in
                         (FStar_String.length f1) - uu____1852  in
                       uu____1851 - (Prims.parse_int "1")  in
                     FStar_String.substring f1 (Prims.parse_int "0")
                       uu____1850
                      in
                   (FStar_String.lowercase f2) = m) uu____1845
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
  
let dont_gen_projectors : Prims.string -> Prims.bool =
  fun m  ->
    let uu____1863 = get___temp_no_proj ()  in
    FStar_List.contains m uu____1863
  
let should_print_message : Prims.string -> Prims.bool =
  fun m  ->
    let uu____1868 = should_verify m  in
    if uu____1868 then m <> "Prims" else false
  
let include_path : Prims.unit -> Prims.string Prims.list =
  fun uu____1873  ->
    let uu____1874 = get_no_default_includes ()  in
    if uu____1874
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____1880 =
         let uu____1882 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____1882
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____1889 =
         let uu____1891 = get_include ()  in
         FStar_List.append uu____1891 ["."]  in
       FStar_List.append uu____1880 uu____1889)
  
let find_file : Prims.string -> Prims.string Prims.option =
  fun filename  ->
    let uu____1897 = FStar_Util.is_path_absolute filename  in
    if uu____1897
    then (if FStar_Util.file_exists filename then Some filename else None)
    else
      (let uu____1902 =
         let uu____1904 = include_path ()  in FStar_List.rev uu____1904  in
       FStar_Util.find_map uu____1902
         (fun p  ->
            let path = FStar_Util.join_paths p filename  in
            if FStar_Util.file_exists path then Some path else None))
  
let prims : Prims.unit -> Prims.string =
  fun uu____1912  ->
    let uu____1913 = get_prims ()  in
    match uu____1913 with
    | None  ->
        let filename = "prims.fst"  in
        let uu____1916 = find_file filename  in
        (match uu____1916 with
         | Some result -> result
         | None  ->
             let uu____1919 =
               let uu____1920 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename
                  in
               FStar_Util.Failure uu____1920  in
             Prims.raise uu____1919)
    | Some x -> x
  
let prims_basename : Prims.unit -> Prims.string =
  fun uu____1924  ->
    let uu____1925 = prims ()  in FStar_Util.basename uu____1925
  
let prepend_output_dir : Prims.string -> Prims.string =
  fun fname  ->
    let uu____1929 = get_odir ()  in
    match uu____1929 with
    | None  -> fname
    | Some x -> Prims.strcat x (Prims.strcat "/" fname)
  
let __temp_no_proj : Prims.string -> Prims.bool =
  fun s  ->
    let uu____1935 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____1935 (FStar_List.contains s)
  
let admit_smt_queries : Prims.unit -> Prims.bool =
  fun uu____1940  -> get_admit_smt_queries () 
let check_cardinality : Prims.unit -> Prims.bool =
  fun uu____1943  ->
    let uu____1944 = get_cardinality ()  in uu____1944 = "check"
  
let codegen : Prims.unit -> Prims.string Prims.option =
  fun uu____1948  -> get_codegen () 
let codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____1953  ->
    let uu____1954 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____1954
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let debug_any : Prims.unit -> Prims.bool =
  fun uu____1963  -> let uu____1964 = get_debug ()  in uu____1964 <> [] 
let debug_at_level : Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      ((modul = "") ||
         (let uu____1973 = get_debug ()  in
          FStar_All.pipe_right uu____1973 (FStar_List.contains modul)))
        && (debug_level_geq level)
  
let dep : Prims.unit -> Prims.string Prims.option =
  fun uu____1979  -> get_dep () 
let detail_errors : Prims.unit -> Prims.bool =
  fun uu____1982  -> get_detail_errors () 
let doc : Prims.unit -> Prims.bool = fun uu____1985  -> get_doc () 
let dump_module : Prims.string -> Prims.bool =
  fun s  ->
    let uu____1989 = get_dump_module ()  in
    FStar_All.pipe_right uu____1989 (FStar_List.contains s)
  
let eager_inference : Prims.unit -> Prims.bool =
  fun uu____1994  -> get_eager_inference () 
let explicit_deps : Prims.unit -> Prims.bool =
  fun uu____1997  -> get_explicit_deps () 
let extract_all : Prims.unit -> Prims.bool =
  fun uu____2000  -> get_extract_all () 
let fs_typ_app : Prims.string -> Prims.bool =
  fun filename  ->
    let uu____2004 = FStar_ST.read light_off_files  in
    FStar_List.contains filename uu____2004
  
let full_context_dependency : Prims.unit -> Prims.bool =
  fun uu____2011  -> true 
let hide_genident_nums : Prims.unit -> Prims.bool =
  fun uu____2014  -> get_hide_genident_nums () 
let hide_uvar_nums : Prims.unit -> Prims.bool =
  fun uu____2017  -> get_hide_uvar_nums () 
let hint_info : Prims.unit -> Prims.bool =
  fun uu____2020  -> get_hint_info () 
let indent : Prims.unit -> Prims.bool = fun uu____2023  -> get_indent () 
let initial_fuel : Prims.unit -> Prims.int =
  fun uu____2026  ->
    let uu____2027 = get_initial_fuel ()  in
    let uu____2028 = get_max_fuel ()  in Prims.min uu____2027 uu____2028
  
let initial_ifuel : Prims.unit -> Prims.int =
  fun uu____2031  ->
    let uu____2032 = get_initial_ifuel ()  in
    let uu____2033 = get_max_ifuel ()  in Prims.min uu____2032 uu____2033
  
let inline_arith : Prims.unit -> Prims.bool =
  fun uu____2036  -> get_inline_arith () 
let interactive : Prims.unit -> Prims.bool = fun uu____2039  -> get_in () 
let lax : Prims.unit -> Prims.bool = fun uu____2042  -> get_lax () 
let log_queries : Prims.unit -> Prims.bool =
  fun uu____2045  -> get_log_queries () 
let log_types : Prims.unit -> Prims.bool =
  fun uu____2048  -> get_log_types () 
let max_fuel : Prims.unit -> Prims.int = fun uu____2051  -> get_max_fuel () 
let max_ifuel : Prims.unit -> Prims.int = fun uu____2054  -> get_max_ifuel () 
let min_fuel : Prims.unit -> Prims.int = fun uu____2057  -> get_min_fuel () 
let ml_ish : Prims.unit -> Prims.bool = fun uu____2060  -> get_MLish () 
let set_ml_ish : Prims.unit -> Prims.unit =
  fun uu____2063  -> set_option "MLish" (Bool true) 
let n_cores : Prims.unit -> Prims.int = fun uu____2066  -> get_n_cores () 
let no_default_includes : Prims.unit -> Prims.bool =
  fun uu____2069  -> get_no_default_includes () 
let no_extract : Prims.string -> Prims.bool =
  fun s  ->
    let uu____2073 = get_no_extract ()  in
    FStar_All.pipe_right uu____2073 (FStar_List.contains s)
  
let no_location_info : Prims.unit -> Prims.bool =
  fun uu____2078  -> get_no_location_info () 
let norm_then_print : Prims.unit -> Prims.bool =
  fun uu____2081  ->
    let uu____2082 = get_print_before_norm ()  in uu____2082 = false
  
let output_dir : Prims.unit -> Prims.string Prims.option =
  fun uu____2086  -> get_odir () 
let print_bound_var_types : Prims.unit -> Prims.bool =
  fun uu____2089  -> get_print_bound_var_types () 
let print_effect_args : Prims.unit -> Prims.bool =
  fun uu____2092  -> get_print_effect_args () 
let print_fuels : Prims.unit -> Prims.bool =
  fun uu____2095  -> get_print_fuels () 
let print_implicits : Prims.unit -> Prims.bool =
  fun uu____2098  -> get_print_implicits () 
let print_real_names : Prims.unit -> Prims.bool =
  fun uu____2101  -> (get_prn ()) || (get_print_full_names ()) 
let print_universes : Prims.unit -> Prims.bool =
  fun uu____2104  -> get_print_universes () 
let print_z3_statistics : Prims.unit -> Prims.bool =
  fun uu____2107  -> get_print_z3_statistics () 
let record_hints : Prims.unit -> Prims.bool =
  fun uu____2110  -> get_record_hints () 
let reuse_hint_for : Prims.unit -> Prims.string Prims.option =
  fun uu____2114  -> get_reuse_hint_for () 
let silent : Prims.unit -> Prims.bool = fun uu____2117  -> get_silent () 
let split_cases : Prims.unit -> Prims.int =
  fun uu____2120  -> get_split_cases () 
let timing : Prims.unit -> Prims.bool = fun uu____2123  -> get_timing () 
let trace_error : Prims.unit -> Prims.bool =
  fun uu____2126  -> get_trace_error () 
let unthrottle_inductives : Prims.unit -> Prims.bool =
  fun uu____2129  -> get_unthrottle_inductives () 
let use_eq_at_higher_order : Prims.unit -> Prims.bool =
  fun uu____2132  -> get_use_eq_at_higher_order () 
let use_hints : Prims.unit -> Prims.bool =
  fun uu____2135  -> get_use_hints () 
let use_tactics : Prims.unit -> Prims.bool =
  fun uu____2138  -> get_use_tactics () 
let verify_all : Prims.unit -> Prims.bool =
  fun uu____2141  -> get_verify_all () 
let verify_module : Prims.unit -> Prims.string Prims.list =
  fun uu____2145  -> get_verify_module () 
let warn_cardinality : Prims.unit -> Prims.bool =
  fun uu____2148  ->
    let uu____2149 = get_cardinality ()  in uu____2149 = "warn"
  
let warn_default_effects : Prims.unit -> Prims.bool =
  fun uu____2152  -> get_warn_default_effects () 
let warn_top_level_effects : Prims.unit -> Prims.bool =
  fun uu____2155  -> get_warn_top_level_effects () 
let z3_exe : Prims.unit -> Prims.string =
  fun uu____2158  ->
    let uu____2159 = get_smt ()  in
    match uu____2159 with | None  -> FStar_Platform.exe "z3" | Some s -> s
  
let z3_cliopt : Prims.unit -> Prims.string Prims.list =
  fun uu____2165  -> get_z3cliopt () 
let z3_refresh : Prims.unit -> Prims.bool =
  fun uu____2168  -> get_z3refresh () 
let z3_rlimit : Prims.unit -> Prims.int = fun uu____2171  -> get_z3rlimit () 
let z3_seed : Prims.unit -> Prims.int = fun uu____2174  -> get_z3seed () 
let z3_timeout : Prims.unit -> Prims.int =
  fun uu____2177  -> get_z3timeout () 
let no_positivity : Prims.unit -> Prims.bool =
  fun uu____2180  -> get_no_positivity () 
let should_extract : Prims.string -> Prims.bool =
  fun m  ->
    (let uu____2184 = no_extract m  in Prims.op_Negation uu____2184) &&
      ((extract_all ()) ||
         (let uu____2185 = get_extract_module ()  in
          match uu____2185 with
          | [] ->
              let uu____2187 = get_extract_namespace ()  in
              (match uu____2187 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
  