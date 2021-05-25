open Prims
let profile : 'uuuuu . (unit -> 'uuuuu) -> Prims.string -> 'uuuuu =
  fun f -> fun c -> FStar_Profiling.profile f FStar_Pervasives_Native.None c
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee -> match projectee with | VerifyAll -> true | uu___ -> false
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyUserList -> true | uu___ -> false
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyFigureItOut -> true | uu___ -> false
type intf_and_impl =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)
type files_for_module_name = intf_and_impl FStar_Util.smap
let (intf_and_impl_to_string :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun ii ->
    match ii with
    | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
        "<None>, <None>"
    | (FStar_Pervasives_Native.Some intf, FStar_Pervasives_Native.None) ->
        intf
    | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some impl) ->
        impl
    | (FStar_Pervasives_Native.Some intf, FStar_Pervasives_Native.Some impl)
        ->
        let uu___ = FStar_String.op_Hat ", " impl in
        FStar_String.op_Hat intf uu___
let (files_for_module_name_to_string : files_for_module_name -> unit) =
  fun m ->
    FStar_Util.print_string "Printing the file system map {\n";
    (let str_opt_to_string sopt =
       match sopt with
       | FStar_Pervasives_Native.None -> "<None>"
       | FStar_Pervasives_Native.Some s -> s in
     FStar_Util.smap_iter m
       (fun k ->
          fun v ->
            let uu___2 = intf_and_impl_to_string v in
            FStar_Util.print2 "%s:%s\n" k uu___2);
     FStar_Util.print_string "}\n")
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee -> match projectee with | White -> true | uu___ -> false
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee -> match projectee with | Gray -> true | uu___ -> false
let (uu___is_Black : color -> Prims.bool) =
  fun projectee -> match projectee with | Black -> true | uu___ -> false
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu___ -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu___ -> false
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu___ =
             (l > lext) &&
               (let uu___1 = FStar_String.substring f (l - lext) lext in
                uu___1 = ext) in
           if uu___
           then
             let uu___1 = FStar_String.substring f Prims.int_zero (l - lext) in
             FStar_Pervasives_Native.Some uu___1
           else FStar_Pervasives_Native.None) suffixes in
    let uu___ = FStar_List.filter FStar_Util.is_some matches in
    match uu___ with
    | (FStar_Pervasives_Native.Some m)::uu___1 ->
        FStar_Pervasives_Native.Some m
    | uu___1 -> FStar_Pervasives_Native.None
let (is_interface : Prims.string -> Prims.bool) =
  fun f ->
    let uu___ = FStar_String.get f ((FStar_String.length f) - Prims.int_one) in
    uu___ = 105
let (is_implementation : Prims.string -> Prims.bool) =
  fun f -> let uu___ = is_interface f in Prims.op_Negation uu___
let list_of_option :
  'uuuuu . 'uuuuu FStar_Pervasives_Native.option -> 'uuuuu Prims.list =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None -> []
let list_of_pair :
  'uuuuu .
    ('uuuuu FStar_Pervasives_Native.option * 'uuuuu
      FStar_Pervasives_Native.option) -> 'uuuuu Prims.list
  =
  fun uu___ ->
    match uu___ with
    | (intf, impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f ->
    let uu___ =
      let uu___1 = FStar_Util.basename f in check_and_strip_suffix uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 = FStar_Util.format1 "not a valid FStar file: %s" f in
          (FStar_Errors.Fatal_NotValidFStarFile, uu___2) in
        FStar_Errors.raise_err uu___1
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f -> let uu___ = module_name_of_file f in FStar_String.lowercase uu___
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f ->
    let lid =
      let uu___ = FStar_Ident.path_of_text f in
      FStar_Ident.lid_of_path uu___ FStar_Range.dummyRange in
    let uu___ = FStar_Ident.ns_of_lid lid in
    match uu___ with
    | [] -> FStar_Pervasives_Native.None
    | ns ->
        let uu___1 = FStar_Ident.lid_of_ids ns in
        FStar_Pervasives_Native.Some uu___1
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | UseInterface _0 -> true | uu___ -> false
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | UseInterface _0 -> _0
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | PreferInterface _0 -> true | uu___ -> false
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | PreferInterface _0 -> _0
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | UseImplementation _0 -> true | uu___ -> false
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | UseImplementation _0 -> _0
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | FriendImplementation _0 -> true | uu___ -> false
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | FriendImplementation _0 -> _0
let (dep_to_string : dependence -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
type dependences = dependence Prims.list
let empty_dependences : 'uuuuu . unit -> 'uuuuu Prims.list = fun uu___ -> []
type dep_node = {
  edges: dependences ;
  color: color }
let (__proj__Mkdep_node__item__edges : dep_node -> dependences) =
  fun projectee -> match projectee with | { edges; color = color1;_} -> edges
let (__proj__Mkdep_node__item__color : dep_node -> color) =
  fun projectee ->
    match projectee with | { edges; color = color1;_} -> color1
type dependence_graph =
  | Deps of dep_node FStar_Util.smap 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee -> true
let (__proj__Deps__item___0 : dependence_graph -> dep_node FStar_Util.smap) =
  fun projectee -> match projectee with | Deps _0 -> _0
type parsing_data_elt =
  | P_begin_module of FStar_Ident.lident 
  | P_open of (Prims.bool * FStar_Ident.lident) 
  | P_implicit_open_module_or_namespace of (open_kind * FStar_Ident.lid) 
  | P_dep of (Prims.bool * FStar_Ident.lident) 
  | P_alias of (FStar_Ident.ident * FStar_Ident.lident) 
  | P_lid of FStar_Ident.lident 
  | P_inline_for_extraction 
let (uu___is_P_begin_module : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_begin_module _0 -> true | uu___ -> false
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee -> match projectee with | P_begin_module _0 -> _0
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_open _0 -> true | uu___ -> false
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee -> match projectee with | P_open _0 -> _0
let (uu___is_P_implicit_open_module_or_namespace :
  parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with
    | P_implicit_open_module_or_namespace _0 -> true
    | uu___ -> false
let (__proj__P_implicit_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStar_Ident.lid)) =
  fun projectee ->
    match projectee with | P_implicit_open_module_or_namespace _0 -> _0
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_dep _0 -> true | uu___ -> false
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee -> match projectee with | P_dep _0 -> _0
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_alias _0 -> true | uu___ -> false
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee -> match projectee with | P_alias _0 -> _0
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_lid _0 -> true | uu___ -> false
let (__proj__P_lid__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee -> match projectee with | P_lid _0 -> _0
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_inline_for_extraction -> true | uu___ -> false
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee -> true
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee -> match projectee with | Mk_pd _0 -> _0
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt ->
    let str_of_open_kind uu___ =
      match uu___ with
      | Open_module -> "P_open_module"
      | Open_namespace -> "P_open_namespace" in
    match elt with
    | P_begin_module lid ->
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid lid in
          FStar_String.op_Hat uu___1 ")" in
        FStar_String.op_Hat "P_begin_module (" uu___
    | P_open (b, lid) ->
        let uu___ =
          let uu___1 = FStar_Util.string_of_bool b in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Ident.string_of_lid lid in
              FStar_String.op_Hat uu___4 ")" in
            FStar_String.op_Hat ", " uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "P_open (" uu___
    | P_implicit_open_module_or_namespace (k, lid) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Ident.string_of_lid lid in
              FStar_String.op_Hat uu___3 ")" in
            FStar_String.op_Hat ", " uu___2 in
          FStar_String.op_Hat (str_of_open_kind k) uu___1 in
        FStar_String.op_Hat "P_implicit_open_module_or_namespace (" uu___
    | P_dep (b, lid) ->
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid lid in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Util.string_of_bool b in
              FStar_String.op_Hat uu___4 ")" in
            FStar_String.op_Hat ", " uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "P_dep (" uu___
    | P_alias (id, lid) ->
        let uu___ =
          let uu___1 = FStar_Ident.string_of_id id in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Ident.string_of_lid lid in
              FStar_String.op_Hat uu___4 ")" in
            FStar_String.op_Hat ", " uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "P_alias (" uu___
    | P_lid lid ->
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid lid in
          FStar_String.op_Hat uu___1 ")" in
        FStar_String.op_Hat "P_lid (" uu___
    | P_inline_for_extraction -> "P_inline_for_extraction"
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s ->
                fun elt ->
                  let uu___1 =
                    let uu___2 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt in
                    FStar_String.op_Hat "; " uu___2 in
                  FStar_String.op_Hat s uu___1) "")
let (parsing_data_elt_eq :
  parsing_data_elt -> parsing_data_elt -> Prims.bool) =
  fun e1 ->
    fun e2 ->
      match (e1, e2) with
      | (P_begin_module l1, P_begin_module l2) ->
          FStar_Ident.lid_equals l1 l2
      | (P_open (b1, l1), P_open (b2, l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_implicit_open_module_or_namespace (k1, l1),
         P_implicit_open_module_or_namespace (k2, l2)) ->
          (k1 = k2) && (FStar_Ident.lid_equals l1 l2)
      | (P_dep (b1, l1), P_dep (b2, l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_alias (i1, l1), P_alias (i2, l2)) ->
          (let uu___ = FStar_Ident.string_of_id i1 in
           let uu___1 = FStar_Ident.string_of_id i2 in uu___ = uu___1) &&
            (FStar_Ident.lid_equals l1 l2)
      | (P_lid l1, P_lid l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction, P_inline_for_extraction) -> true
      | (uu___, uu___1) -> false
let (empty_parsing_data : parsing_data) = Mk_pd []
type deps =
  {
  dep_graph: dependence_graph ;
  file_system_map: files_for_module_name ;
  cmd_line_files: file_name Prims.list ;
  all_files: file_name Prims.list ;
  interfaces_with_inlining: module_name Prims.list ;
  parse_results: parsing_data FStar_Util.smap }
let (__proj__Mkdeps__item__dep_graph : deps -> dependence_graph) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> dep_graph
let (__proj__Mkdeps__item__file_system_map : deps -> files_for_module_name) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> file_system_map
let (__proj__Mkdeps__item__cmd_line_files : deps -> file_name Prims.list) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> cmd_line_files
let (__proj__Mkdeps__item__all_files : deps -> file_name Prims.list) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> all_files
let (__proj__Mkdeps__item__interfaces_with_inlining :
  deps -> module_name Prims.list) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} ->
        interfaces_with_inlining
let (__proj__Mkdeps__item__parse_results :
  deps -> parsing_data FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> parse_results
let (deps_try_find :
  dependence_graph -> Prims.string -> dep_node FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    fun k -> match uu___ with | Deps m -> FStar_Util.smap_try_find m k
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu___ ->
    fun k -> fun v -> match uu___ with | Deps m -> FStar_Util.smap_add m k v
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu___ -> match uu___ with | Deps m -> FStar_Util.smap_keys m
let (deps_empty : unit -> dependence_graph) =
  fun uu___ ->
    let uu___1 = FStar_Util.smap_create (Prims.of_int (41)) in Deps uu___1
let (mk_deps :
  dependence_graph ->
    files_for_module_name ->
      file_name Prims.list ->
        file_name Prims.list ->
          module_name Prims.list -> parsing_data FStar_Util.smap -> deps)
  =
  fun dg ->
    fun fs ->
      fun c ->
        fun a ->
          fun i ->
            fun pr ->
              {
                dep_graph = dg;
                file_system_map = fs;
                cmd_line_files = c;
                all_files = a;
                interfaces_with_inlining = i;
                parse_results = pr
              }
let (empty_deps : deps) =
  let uu___ = deps_empty () in
  let uu___1 = FStar_Util.smap_create Prims.int_zero in
  let uu___2 = FStar_Util.smap_create Prims.int_zero in
  mk_deps uu___ uu___1 [] [] [] uu___2
let (module_name_of_dep : dependence -> module_name) =
  fun uu___ ->
    match uu___ with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
    | FriendImplementation m -> m
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = FStar_Util.smap_try_find file_system_map key in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn, uu___1) ->
          let uu___2 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu___2
      | FStar_Pervasives_Native.Some
          (uu___1, FStar_Pervasives_Native.Some fn) ->
          let uu___2 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu___2
      | uu___1 -> FStar_Pervasives_Native.None
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = FStar_Util.smap_try_find file_system_map key in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface, uu___1) ->
          FStar_Pervasives_Native.Some iface
      | uu___1 -> FStar_Pervasives_Native.None
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = FStar_Util.smap_try_find file_system_map key in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (uu___1, FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu___1 -> FStar_Pervasives_Native.None
let (interface_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps1 -> fun key -> interface_of_internal deps1.file_system_map key
let (implementation_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps1 ->
    fun key -> implementation_of_internal deps1.file_system_map key
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map ->
    fun key ->
      let uu___ = interface_of_internal file_system_map key in
      FStar_Option.isSome uu___
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = implementation_of_internal file_system_map key in
      FStar_Option.isSome uu___
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax = FStar_Options.lax () in
    let cache_fn =
      if lax
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked" in
    let mname = FStar_All.pipe_right fn module_name_of_file in
    let uu___ =
      let uu___1 = FStar_All.pipe_right cache_fn FStar_Util.basename in
      FStar_Options.find_file uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn in
        ((let uu___2 =
            ((let uu___3 = FStar_Options.dep () in FStar_Option.isSome uu___3)
               &&
               (let uu___3 = FStar_Options.should_be_already_cached mname in
                Prims.op_Negation uu___3))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu___3 =
                    FStar_Util.paths_to_same_file path expected_cache_file in
                  Prims.op_Negation uu___3)) in
          if uu___2
          then
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Options.prepend_cache_dir cache_fn in
                FStar_Util.format3
                  "Did not expect %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu___5 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu___4) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___3
          else ());
         (let uu___2 =
            (FStar_Util.file_exists expected_cache_file) &&
              (FStar_Util.paths_to_same_file path expected_cache_file) in
          if uu___2 then expected_cache_file else path))
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached in
        if uu___1
        then
          let uu___2 =
            let uu___3 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu___3) in
          FStar_Errors.raise_err uu___2
        else FStar_Options.prepend_cache_dir cache_fn in
  let memo = FStar_Util.smap_create (Prims.of_int (100)) in
  let memo1 f x =
    let uu___ = FStar_Util.smap_try_find memo x in
    match uu___ with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None ->
        let res = f x in (FStar_Util.smap_add memo x res; res) in
  memo1 checked_file_and_exists_flag
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps1 ->
    fun fn ->
      let uu___ = FStar_Util.smap_try_find deps1.parse_results fn in
      FStar_All.pipe_right uu___ FStar_Util.must
let (file_of_dep_aux :
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name)
  =
  fun use_checked_file ->
    fun file_system_map ->
      fun all_cmd_line_files ->
        fun d ->
          let cmd_line_has_impl key =
            FStar_All.pipe_right all_cmd_line_files
              (FStar_Util.for_some
                 (fun fn ->
                    (is_implementation fn) &&
                      (let uu___ = lowercase_module_name fn in key = uu___))) in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu___ = interface_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___2 =
                     let uu___3 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingInterface, uu___3) in
                   FStar_Errors.raise_err uu___2
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu___ =
                (cmd_line_has_impl key) &&
                  (let uu___1 = FStar_Options.dep () in
                   FStar_Option.isNone uu___1) in
              if uu___
              then
                let uu___1 = FStar_Options.expose_interfaces () in
                (if uu___1
                 then
                   let uu___2 =
                     let uu___3 =
                       implementation_of_internal file_system_map key in
                     FStar_Option.get uu___3 in
                   maybe_use_cache_of uu___2
                 else
                   (let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            implementation_of_internal file_system_map key in
                          FStar_Option.get uu___6 in
                        let uu___6 =
                          let uu___7 =
                            interface_of_internal file_system_map key in
                          FStar_Option.get uu___7 in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu___5 uu___6 in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu___4) in
                    FStar_Errors.raise_err uu___3))
              else
                (let uu___2 =
                   let uu___3 = interface_of_internal file_system_map key in
                   FStar_Option.get uu___3 in
                 maybe_use_cache_of uu___2)
          | PreferInterface key ->
              let uu___ = implementation_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     let uu___2 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu___2) in
                   FStar_Errors.raise_err uu___1
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu___ = implementation_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     let uu___2 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu___2) in
                   FStar_Errors.raise_err uu___1
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu___ = implementation_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     let uu___2 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu___2) in
                   FStar_Errors.raise_err uu___1
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
let (file_of_dep :
  files_for_module_name -> file_name Prims.list -> dependence -> file_name) =
  file_of_dep_aux false
let (dependences_of :
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list)
  =
  fun file_system_map ->
    fun deps1 ->
      fun all_cmd_line_files ->
        fun fn ->
          let uu___ = deps_try_find deps1 fn in
          match uu___ with
          | FStar_Pervasives_Native.None -> empty_dependences ()
          | FStar_Pervasives_Native.Some { edges = deps2; color = uu___1;_}
              ->
              let uu___2 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files) deps2 in
              FStar_All.pipe_right uu___2
                (FStar_List.filter (fun k -> k <> fn))
let (print_graph : dependence_graph -> unit) =
  fun graph ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu___3 =
       let uu___4 =
         let uu___5 =
           let uu___6 =
             let uu___7 =
               let uu___8 = deps_keys graph in FStar_List.unique uu___8 in
             FStar_List.collect
               (fun k ->
                  let deps1 =
                    let uu___8 =
                      let uu___9 = deps_try_find graph k in
                      FStar_Util.must uu___9 in
                    uu___8.edges in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print dep =
                    let uu___8 =
                      let uu___9 = lowercase_module_name k in r uu___9 in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu___8
                      (r (module_name_of_dep dep)) in
                  FStar_List.map print deps1) uu___7 in
           FStar_String.concat "\n" uu___6 in
         FStar_String.op_Hat uu___5 "\n}\n" in
       FStar_String.op_Hat "digraph {\n" uu___4 in
     FStar_Util.write_file "dep.graph" uu___3)
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu___ ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu___1 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu___1 in
    FStar_List.concatMap
      (fun d ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f ->
                let f1 = FStar_Util.basename f in
                let uu___1 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu___1
                  (FStar_Util.map_option
                     (fun longname ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu___2 =
              let uu___3 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu___3) in
            FStar_Errors.raise_err uu___2)) include_directories2
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames ->
    let map = FStar_Util.smap_create (Prims.of_int (41)) in
    let add_entry key full_path =
      let uu___ = FStar_Util.smap_try_find map key in
      match uu___ with
      | FStar_Pervasives_Native.Some (intf, impl) ->
          let uu___1 = is_interface full_path in
          if uu___1
          then
            FStar_Util.smap_add map key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None ->
          let uu___1 = is_interface full_path in
          if uu___1
          then
            FStar_Util.smap_add map key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu___1 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu___2 ->
          match uu___2 with
          | (longname, full_path) ->
              add_entry (FStar_String.lowercase longname) full_path) uu___1);
    FStar_List.iter
      (fun f -> let uu___2 = lowercase_module_name f in add_entry uu___2 f)
      filenames;
    map
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l ->
    fun last ->
      let suffix =
        if last
        then
          let uu___ =
            let uu___1 = FStar_Ident.ident_of_lid l in
            FStar_Ident.string_of_id uu___1 in
          [uu___]
        else [] in
      let names =
        let uu___ =
          let uu___1 = FStar_Ident.ns_of_lid l in
          FStar_List.map (fun x -> FStar_Ident.string_of_id x) uu___1 in
        FStar_List.append uu___ suffix in
      FStar_String.concat "." names
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l ->
    fun last ->
      let uu___ = string_of_lid l last in FStar_String.lowercase uu___
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Ident.ns_of_lid l in
      FStar_List.map FStar_Ident.string_of_id uu___1 in
    FStar_String.concat "_" uu___
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid ->
    fun filename ->
      let k' = lowercase_join_longident lid true in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Util.basename filename in
              check_and_strip_suffix uu___4 in
            FStar_Util.must uu___3 in
          FStar_String.lowercase uu___2 in
        uu___1 <> k' in
      if uu___
      then
        let uu___1 = FStar_Ident.range_of_lid lid in
        let uu___2 =
          let uu___3 =
            let uu___4 = string_of_lid lid true in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu___4 filename in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu___3) in
        FStar_Errors.log_issue uu___1 uu___2
      else ()
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu___ -> false
let (core_modules : Prims.string Prims.list) =
  let uu___ =
    let uu___1 = FStar_Options.prims_basename () in
    let uu___2 =
      let uu___3 = FStar_Options.pervasives_basename () in
      let uu___4 =
        let uu___5 = FStar_Options.pervasives_native_basename () in [uu___5] in
      uu___3 :: uu___4 in
    uu___1 :: uu___2 in
  FStar_All.pipe_right uu___ (FStar_List.map module_name_of_file)
let (implicit_ns_deps : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.fstar_ns_lid]
let (implicit_module_deps : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.prims_lid; FStar_Parser_Const.pervasives_lid]
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename ->
    let filename = FStar_Util.basename full_filename in
    let implicit_module_deps1 =
      FStar_List.map (fun l -> (l, Open_module)) implicit_module_deps in
    let implicit_ns_deps1 =
      FStar_List.map (fun l -> (l, Open_namespace)) implicit_ns_deps in
    let uu___ =
      let uu___1 = module_name_of_file filename in
      FStar_List.mem uu___1 core_modules in
    if uu___
    then []
    else
      (let uu___2 =
         let uu___3 = lowercase_module_name full_filename in
         namespace_of_module uu___3 in
       match uu___2 with
       | FStar_Pervasives_Native.None ->
           FStar_List.append implicit_ns_deps1 implicit_module_deps1
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_ns_deps1
             (FStar_List.append implicit_module_deps1 [(ns, Open_namespace)]))
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d ->
    fun d' ->
      match (d, d') with
      | (PreferInterface l', FriendImplementation l) -> l = l'
      | uu___ -> d = d'
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool -> Prims.bool)
  =
  fun original_map ->
    fun working_map ->
      fun prefix ->
        fun implicit_open ->
          let found = FStar_Util.mk_ref false in
          let prefix1 = FStar_String.op_Hat prefix "." in
          let suffix_exists mopt =
            match mopt with
            | FStar_Pervasives_Native.None -> false
            | FStar_Pervasives_Native.Some (intf, impl) ->
                (FStar_Util.is_some intf) || (FStar_Util.is_some impl) in
          FStar_Util.smap_iter original_map
            (fun k ->
               fun uu___1 ->
                 if FStar_Util.starts_with k prefix1
                 then
                   let suffix =
                     FStar_String.substring k (FStar_String.length prefix1)
                       ((FStar_String.length k) -
                          (FStar_String.length prefix1)) in
                   ((let suffix_filename =
                       FStar_Util.smap_try_find original_map suffix in
                     if implicit_open && (suffix_exists suffix_filename)
                     then
                       let str =
                         let uu___3 =
                           FStar_All.pipe_right suffix_filename
                             FStar_Util.must in
                         FStar_All.pipe_right uu___3 intf_and_impl_to_string in
                       let uu___3 =
                         let uu___4 =
                           FStar_Util.format4
                             "Implicitly opening %s namespace shadows (%s -> %s), rename %s to avoid conflicts"
                             prefix1 suffix str str in
                         (FStar_Errors.Warning_UnexpectedFile, uu___4) in
                       FStar_Errors.log_issue FStar_Range.dummyRange uu___3
                     else ());
                    (let filename =
                       let uu___3 = FStar_Util.smap_try_find original_map k in
                       FStar_Util.must uu___3 in
                     FStar_Util.smap_add working_map suffix filename;
                     FStar_ST.op_Colon_Equals found true))
                 else ());
          FStar_ST.op_Bang found
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        (parsing_data * dependence Prims.list * Prims.bool * dependence
          Prims.list))
  =
  fun original_map ->
    fun filename ->
      fun get_parsing_data_from_cache ->
        let from_parsing_data pd original_map1 filename1 =
          let deps1 = FStar_Util.mk_ref [] in
          let has_inline_for_extraction = FStar_Util.mk_ref false in
          let mo_roots =
            let mname = lowercase_module_name filename1 in
            let uu___ =
              (is_interface filename1) &&
                (has_implementation original_map1 mname) in
            if uu___ then [UseImplementation mname] else [] in
          let auto_open =
            let uu___ = hard_coded_dependencies filename1 in
            FStar_All.pipe_right uu___
              (FStar_List.map
                 (fun uu___1 ->
                    match uu___1 with
                    | (lid, k) ->
                        P_implicit_open_module_or_namespace (k, lid))) in
          let working_map = FStar_Util.smap_copy original_map1 in
          let set_interface_inlining uu___ =
            let uu___1 = is_interface filename1 in
            if uu___1
            then FStar_ST.op_Colon_Equals has_inline_for_extraction true
            else () in
          let add_dep deps2 d =
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_ST.op_Bang deps2 in
                FStar_List.existsML (dep_subsumed_by d) uu___2 in
              Prims.op_Negation uu___1 in
            if uu___
            then
              let uu___1 = let uu___2 = FStar_ST.op_Bang deps2 in d :: uu___2 in
              FStar_ST.op_Colon_Equals deps2 uu___1
            else () in
          let dep_edge module_name1 is_friend =
            if is_friend
            then FriendImplementation module_name1
            else PreferInterface module_name1 in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true in
            let uu___ = resolve_module_name original_or_working_map key in
            match uu___ with
            | FStar_Pervasives_Native.Some module_name1 ->
                (add_dep deps1 (dep_edge module_name1 is_friend); true)
            | uu___1 -> false in
          let record_open_module let_open lid =
            let uu___ =
              (let_open && (add_dependence_edge working_map lid false)) ||
                ((Prims.op_Negation let_open) &&
                   (add_dependence_edge original_map1 lid false)) in
            if uu___
            then true
            else
              (if let_open
               then
                 (let uu___3 = FStar_Ident.range_of_lid lid in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = string_of_lid lid true in
                      FStar_Util.format1 "Module not found: %s" uu___6 in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu___5) in
                  FStar_Errors.log_issue uu___3 uu___4)
               else ();
               false) in
          let record_open_namespace lid implicit_open =
            let key = lowercase_join_longident lid true in
            let r =
              enter_namespace original_map1 working_map key implicit_open in
            if (Prims.op_Negation r) && (Prims.op_Negation implicit_open)
            then
              let uu___ = FStar_Ident.range_of_lid lid in
              let uu___1 =
                let uu___2 =
                  let uu___3 = string_of_lid lid true in
                  FStar_Util.format1
                    "No modules in namespace %s and no file with that name either"
                    uu___3 in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu___2) in
              FStar_Errors.log_issue uu___ uu___1
            else () in
          let record_open let_open lid =
            let uu___ = record_open_module let_open lid in
            if uu___
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid false
              else () in
          let record_implicit_open_module_or_namespace uu___ =
            match uu___ with
            | (lid, kind) ->
                (match kind with
                 | Open_namespace -> record_open_namespace lid true
                 | Open_module ->
                     let uu___1 = record_open_module false lid in ()) in
          let record_module_alias ident lid =
            let key =
              let uu___ = FStar_Ident.string_of_id ident in
              FStar_String.lowercase uu___ in
            let alias = lowercase_join_longident lid true in
            let uu___ = FStar_Util.smap_try_find original_map1 alias in
            match uu___ with
            | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                (FStar_Util.smap_add working_map key deps_of_aliased_module;
                 (let uu___3 =
                    let uu___4 = lowercase_join_longident lid true in
                    dep_edge uu___4 false in
                  add_dep deps1 uu___3);
                 true)
            | FStar_Pervasives_Native.None ->
                ((let uu___2 = FStar_Ident.range_of_lid lid in
                  let uu___3 =
                    let uu___4 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu___4) in
                  FStar_Errors.log_issue uu___2 uu___3);
                 false) in
          let add_dep_on_module module_name1 is_friend =
            let uu___ =
              add_dependence_edge working_map module_name1 is_friend in
            if uu___
            then ()
            else
              (let uu___2 =
                 FStar_Options.debug_at_level_no_module
                   (FStar_Options.Other "Dep") in
               if uu___2
               then
                 let uu___3 = FStar_Ident.range_of_lid module_name1 in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Ident.string_of_lid module_name1 in
                     FStar_Util.format1 "Unbound module reference %s" uu___6 in
                   (FStar_Errors.Warning_UnboundModuleReference, uu___5) in
                 FStar_Errors.log_issue uu___3 uu___4
               else ()) in
          let record_lid lid =
            let uu___ = FStar_Ident.ns_of_lid lid in
            match uu___ with
            | [] -> ()
            | ns ->
                let module_name1 = FStar_Ident.lid_of_ids ns in
                add_dep_on_module module_name1 false in
          let begin_module lid =
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Ident.ns_of_lid lid in
                FStar_List.length uu___2 in
              uu___1 > Prims.int_zero in
            if uu___
            then
              let uu___1 =
                let uu___2 = namespace_of_lid lid in
                enter_namespace original_map1 working_map uu___2 in
              ()
            else () in
          (match pd with
           | Mk_pd l ->
               FStar_All.pipe_right (FStar_List.append auto_open l)
                 (FStar_List.iter
                    (fun elt ->
                       match elt with
                       | P_begin_module lid -> begin_module lid
                       | P_open (b, lid) -> record_open b lid
                       | P_implicit_open_module_or_namespace (k, lid) ->
                           record_implicit_open_module_or_namespace (lid, k)
                       | P_dep (b, lid) -> add_dep_on_module lid b
                       | P_alias (id, lid) ->
                           let uu___1 = record_module_alias id lid in ()
                       | P_lid lid -> record_lid lid
                       | P_inline_for_extraction -> set_interface_inlining ())));
          (let uu___1 = FStar_ST.op_Bang deps1 in
           let uu___2 = FStar_ST.op_Bang has_inline_for_extraction in
           (uu___1, uu___2, mo_roots)) in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache in
        let uu___ = FStar_All.pipe_right data_from_cache FStar_Util.is_some in
        if uu___
        then
          ((let uu___2 =
              FStar_Options.debug_at_level_no_module
                (FStar_Options.Other "Dep") in
            if uu___2
            then
              FStar_Util.print1
                "Reading the parsing data for %s from its checked file\n"
                filename
            else ());
           (let uu___2 =
              let uu___3 =
                FStar_All.pipe_right data_from_cache FStar_Util.must in
              from_parsing_data uu___3 original_map filename in
            match uu___2 with
            | (deps1, has_inline_for_extraction, mo_roots) ->
                let uu___3 =
                  FStar_All.pipe_right data_from_cache FStar_Util.must in
                (uu___3, deps1, has_inline_for_extraction, mo_roots)))
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref Prims.int_zero in
           let pd = FStar_Util.mk_ref [] in
           let add_to_parsing_data elt =
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_ST.op_Bang pd in
                 FStar_List.existsML (fun e -> parsing_data_elt_eq e elt)
                   uu___4 in
               Prims.op_Negation uu___3 in
             if uu___2
             then
               let uu___3 = let uu___4 = FStar_ST.op_Bang pd in elt :: uu___4 in
               FStar_ST.op_Colon_Equals pd uu___3
             else () in
           let rec collect_module uu___2 =
             match uu___2 with
             | FStar_Parser_AST.Module (lid, decls) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
             | FStar_Parser_AST.Interface (lid, decls, uu___3) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
           and collect_decls decls =
             FStar_List.iter
               (fun x ->
                  collect_decl x.FStar_Parser_AST.d;
                  FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                  (match x.FStar_Parser_AST.d with
                   | FStar_Parser_AST.Val uu___4 when
                       FStar_List.contains
                         FStar_Parser_AST.Inline_for_extraction
                         x.FStar_Parser_AST.quals
                       -> add_to_parsing_data P_inline_for_extraction
                   | uu___4 -> ())) decls
           and collect_decl d =
             match d with
             | FStar_Parser_AST.Include lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Open lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Friend lid ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = lowercase_join_longident lid true in
                       FStar_All.pipe_right uu___5 FStar_Ident.lid_of_str in
                     (true, uu___4) in
                   P_dep uu___3 in
                 add_to_parsing_data uu___2
             | FStar_Parser_AST.ModuleAbbrev (ident, lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStar_Parser_AST.TopLevelLet (uu___2, patterms) ->
                 FStar_List.iter
                   (fun uu___3 ->
                      match uu___3 with
                      | (pat, t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStar_Parser_AST.Splice (uu___2, t) -> collect_term t
             | FStar_Parser_AST.Assume (uu___2, t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu___2;
                   FStar_Parser_AST.mdest = uu___3;
                   FStar_Parser_AST.lift_op =
                     FStar_Parser_AST.NonReifiableLift t;_}
                 -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu___2;
                   FStar_Parser_AST.mdest = uu___3;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                 -> collect_term t
             | FStar_Parser_AST.Val (uu___2, t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu___2;
                   FStar_Parser_AST.mdest = uu___3;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                     (t0, t1);_}
                 -> (collect_term t0; collect_term t1)
             | FStar_Parser_AST.Tycon (uu___2, tc, ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStar_Parser_Const.mk_class_lid)
                  else ();
                  FStar_List.iter collect_tycon ts)
             | FStar_Parser_AST.Exception (uu___2, t) ->
                 FStar_Util.iter_opt t collect_term
             | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.LayeredEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.Polymonadic_bind (uu___2, uu___3, uu___4, t)
                 -> collect_term t
             | FStar_Parser_AST.Polymonadic_subcomp (uu___2, uu___3, t) ->
                 collect_term t
             | FStar_Parser_AST.Pragma uu___2 -> ()
             | FStar_Parser_AST.TopLevelModule lid ->
                 (FStar_Util.incr num_of_toplevelmods;
                  (let uu___3 =
                     let uu___4 = FStar_ST.op_Bang num_of_toplevelmods in
                     uu___4 > Prims.int_one in
                   if uu___3
                   then
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = string_of_lid lid true in
                         FStar_Util.format1
                           "Automatic dependency analysis demands one module per file (module %s not supported)"
                           uu___6 in
                       (FStar_Errors.Fatal_OneModulePerFile, uu___5) in
                     let uu___5 = FStar_Ident.range_of_lid lid in
                     FStar_Errors.raise_error uu___4 uu___5
                   else ()))
           and collect_tycon uu___2 =
             match uu___2 with
             | FStar_Parser_AST.TyconAbstract (uu___3, binders, k) ->
                 (collect_binders binders; FStar_Util.iter_opt k collect_term)
             | FStar_Parser_AST.TyconAbbrev (uu___3, binders, k, t) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  collect_term t)
             | FStar_Parser_AST.TyconRecord (uu___3, binders, k, identterms)
                 ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu___6 ->
                       match uu___6 with
                       | (uu___7, aq, attrs, t) ->
                           (collect_aqual aq;
                            FStar_All.pipe_right attrs
                              (FStar_List.iter collect_term);
                            collect_term t)) identterms)
             | FStar_Parser_AST.TyconVariant (uu___3, binders, k, identterms)
                 ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu___6 ->
                       match uu___6 with
                       | (uu___7, t, uu___8) ->
                           FStar_Util.iter_opt t collect_term) identterms)
           and collect_effect_decl uu___2 =
             match uu___2 with
             | FStar_Parser_AST.DefineEffect (uu___3, binders, t, decls) ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStar_Parser_AST.RedefineEffect (uu___3, binders, t) ->
                 (collect_binders binders; collect_term t)
           and collect_binders binders =
             FStar_List.iter collect_binder binders
           and collect_binder b =
             collect_aqual b.FStar_Parser_AST.aqual;
             FStar_All.pipe_right b.FStar_Parser_AST.battributes
               (FStar_List.iter collect_term);
             (match b with
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu___4, t);
                  FStar_Parser_AST.brange = uu___5;
                  FStar_Parser_AST.blevel = uu___6;
                  FStar_Parser_AST.aqual = uu___7;
                  FStar_Parser_AST.battributes = uu___8;_} -> collect_term t
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                    (uu___4, t);
                  FStar_Parser_AST.brange = uu___5;
                  FStar_Parser_AST.blevel = uu___6;
                  FStar_Parser_AST.aqual = uu___7;
                  FStar_Parser_AST.battributes = uu___8;_} -> collect_term t
              | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu___4;
                  FStar_Parser_AST.blevel = uu___5;
                  FStar_Parser_AST.aqual = uu___6;
                  FStar_Parser_AST.battributes = uu___7;_} -> collect_term t
              | uu___4 -> ())
           and collect_aqual uu___2 =
             match uu___2 with
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                 collect_term t
             | uu___3 -> ()
           and collect_term t = collect_term' t.FStar_Parser_AST.tm
           and collect_constant uu___2 =
             match uu___2 with
             | FStar_Const.Const_int
                 (uu___3, FStar_Pervasives_Native.Some (signedness, width))
                 ->
                 let u =
                   match signedness with
                   | FStar_Const.Unsigned -> "u"
                   | FStar_Const.Signed -> "" in
                 let w =
                   match width with
                   | FStar_Const.Int8 -> "8"
                   | FStar_Const.Int16 -> "16"
                   | FStar_Const.Int32 -> "32"
                   | FStar_Const.Int64 -> "64" in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = FStar_Util.format2 "fstar.%sint%s" u w in
                       FStar_All.pipe_right uu___7 FStar_Ident.lid_of_str in
                     (false, uu___6) in
                   P_dep uu___5 in
                 add_to_parsing_data uu___4
             | FStar_Const.Const_char uu___3 ->
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       FStar_All.pipe_right "fstar.char"
                         FStar_Ident.lid_of_str in
                     (false, uu___6) in
                   P_dep uu___5 in
                 add_to_parsing_data uu___4
             | FStar_Const.Const_float uu___3 ->
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       FStar_All.pipe_right "fstar.float"
                         FStar_Ident.lid_of_str in
                     (false, uu___6) in
                   P_dep uu___5 in
                 add_to_parsing_data uu___4
             | uu___3 -> ()
           and collect_term' uu___2 =
             match uu___2 with
             | FStar_Parser_AST.Wild -> ()
             | FStar_Parser_AST.Const c -> collect_constant c
             | FStar_Parser_AST.Op (s, ts) ->
                 ((let uu___4 =
                     let uu___5 = FStar_Ident.string_of_id s in uu___5 = "@" in
                   if uu___4
                   then
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_Ident.path_of_text
                             "FStar.List.Tot.Base.append" in
                         FStar_Ident.lid_of_path uu___7
                           FStar_Range.dummyRange in
                       FStar_Parser_AST.Name uu___6 in
                     collect_term' uu___5
                   else ());
                  FStar_List.iter collect_term ts)
             | FStar_Parser_AST.Tvar uu___3 -> ()
             | FStar_Parser_AST.Uvar uu___3 -> ()
             | FStar_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Projector (lid, uu___3) ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Construct (lid, termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStar_List.iter
                    (fun uu___4 ->
                       match uu___4 with | (t, uu___5) -> collect_term t)
                    termimps)
             | FStar_Parser_AST.Abs (pats, t) ->
                 (collect_patterns pats; collect_term t)
             | FStar_Parser_AST.App (t1, t2, uu___3) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Let (uu___3, patterms, t) ->
                 (FStar_List.iter
                    (fun uu___5 ->
                       match uu___5 with
                       | (attrs_opt, (pat, t1)) ->
                           ((let uu___7 =
                               FStar_Util.map_opt attrs_opt
                                 (FStar_List.iter collect_term) in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStar_Parser_AST.LetOpen (lid, t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStar_Parser_AST.LetOpenRecord (r, rty, e) ->
                 (collect_term r; collect_term rty; collect_term e)
             | FStar_Parser_AST.Bind (uu___3, t1, t2) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Seq (t1, t2) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.If (t1, ret_opt, t2, t3) ->
                 (collect_term t1;
                  FStar_Util.iter_opt ret_opt collect_term;
                  collect_term t2;
                  collect_term t3)
             | FStar_Parser_AST.Match (t, ret_opt, bs) ->
                 (collect_term t;
                  FStar_Util.iter_opt ret_opt collect_term;
                  collect_branches bs)
             | FStar_Parser_AST.TryWith (t, bs) ->
                 (collect_term t; collect_branches bs)
             | FStar_Parser_AST.Ascribed
                 (t1, t2, FStar_Pervasives_Native.None) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Ascribed
                 (t1, t2, FStar_Pervasives_Native.Some tac) ->
                 (collect_term t1; collect_term t2; collect_term tac)
             | FStar_Parser_AST.Record (t, idterms) ->
                 (FStar_Util.iter_opt t collect_term;
                  FStar_List.iter
                    (fun uu___4 ->
                       match uu___4 with | (uu___5, t1) -> collect_term t1)
                    idterms)
             | FStar_Parser_AST.Project (t, uu___3) -> collect_term t
             | FStar_Parser_AST.Product (binders, t) ->
                 (collect_binders binders; collect_term t)
             | FStar_Parser_AST.Sum (binders, t) ->
                 (FStar_List.iter
                    (fun uu___4 ->
                       match uu___4 with
                       | FStar_Pervasives.Inl b -> collect_binder b
                       | FStar_Pervasives.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStar_Parser_AST.QForall (binders, (uu___3, ts), t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.QExists (binders, (uu___3, ts), t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.Refine (binder, t) ->
                 (collect_binder binder; collect_term t)
             | FStar_Parser_AST.NamedTyp (uu___3, t) -> collect_term t
             | FStar_Parser_AST.Paren t -> collect_term t
             | FStar_Parser_AST.Requires (t, uu___3) -> collect_term t
             | FStar_Parser_AST.Ensures (t, uu___3) -> collect_term t
             | FStar_Parser_AST.Labeled (t, uu___3, uu___4) -> collect_term t
             | FStar_Parser_AST.LexList l -> FStar_List.iter collect_term l
             | FStar_Parser_AST.WFOrder (t1, t2) ->
                 ((let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Ident.lid_of_str "FStar.WellFounded" in
                       (false, uu___6) in
                     P_dep uu___5 in
                   add_to_parsing_data uu___4);
                  collect_term t1;
                  collect_term t2)
             | FStar_Parser_AST.Decreases (t, uu___3) -> collect_term t
             | FStar_Parser_AST.Quote (t, uu___3) -> collect_term t
             | FStar_Parser_AST.Antiquote t -> collect_term t
             | FStar_Parser_AST.VQuote t -> collect_term t
             | FStar_Parser_AST.Attributes cattributes ->
                 FStar_List.iter collect_term cattributes
             | FStar_Parser_AST.CalcProof (rel, init, steps) ->
                 ((let uu___4 =
                     let uu___5 =
                       let uu___6 = FStar_Ident.lid_of_str "FStar.Calc" in
                       (false, uu___6) in
                     P_dep uu___5 in
                   add_to_parsing_data uu___4);
                  collect_term rel;
                  collect_term init;
                  FStar_List.iter
                    (fun uu___6 ->
                       match uu___6 with
                       | FStar_Parser_AST.CalcStep (rel1, just, next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
           and collect_patterns ps = FStar_List.iter collect_pattern ps
           and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
           and collect_pattern' uu___2 =
             match uu___2 with
             | FStar_Parser_AST.PatVar (uu___3, aqual, attrs) ->
                 (collect_aqual aqual;
                  FStar_All.pipe_right attrs (FStar_List.iter collect_term))
             | FStar_Parser_AST.PatTvar (uu___3, aqual, attrs) ->
                 (collect_aqual aqual;
                  FStar_All.pipe_right attrs (FStar_List.iter collect_term))
             | FStar_Parser_AST.PatWild (aqual, attrs) ->
                 (collect_aqual aqual;
                  FStar_All.pipe_right attrs (FStar_List.iter collect_term))
             | FStar_Parser_AST.PatOp uu___3 -> ()
             | FStar_Parser_AST.PatConst uu___3 -> ()
             | FStar_Parser_AST.PatApp (p, ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStar_Parser_AST.PatName uu___3 -> ()
             | FStar_Parser_AST.PatList ps -> collect_patterns ps
             | FStar_Parser_AST.PatOr ps -> collect_patterns ps
             | FStar_Parser_AST.PatTuple (ps, uu___3) -> collect_patterns ps
             | FStar_Parser_AST.PatRecord lidpats ->
                 FStar_List.iter
                   (fun uu___3 ->
                      match uu___3 with | (uu___4, p) -> collect_pattern p)
                   lidpats
             | FStar_Parser_AST.PatAscribed
                 (p, (t, FStar_Pervasives_Native.None)) ->
                 (collect_pattern p; collect_term t)
             | FStar_Parser_AST.PatAscribed
                 (p, (t, FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           and collect_branches bs = FStar_List.iter collect_branch bs
           and collect_branch uu___2 =
             match uu___2 with
             | (pat, t1, t2) ->
                 (collect_pattern pat;
                  FStar_Util.iter_opt t1 collect_term;
                  collect_term t2) in
           let uu___2 = FStar_Parser_Driver.parse_file filename in
           match uu___2 with
           | (ast, uu___3) ->
               (collect_module ast;
                (let pd1 =
                   let uu___5 =
                     let uu___6 = FStar_ST.op_Bang pd in
                     FStar_List.rev uu___6 in
                   Mk_pd uu___5 in
                 let uu___5 = from_parsing_data pd1 original_map filename in
                 match uu___5 with
                 | (deps1, has_inline_for_extraction, mo_roots) ->
                     (pd1, deps1, has_inline_for_extraction, mo_roots))))
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu___ = FStar_Util.smap_create Prims.int_zero in
  FStar_Util.mk_ref uu___
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache -> FStar_ST.op_Colon_Equals collect_one_cache cache
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph ->
    let uu___ = dep_graph in
    match uu___ with
    | Deps g -> let uu___1 = FStar_Util.smap_copy g in Deps uu___1
let (widen_deps :
  module_name Prims.list ->
    dependence_graph ->
      files_for_module_name -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun friends ->
    fun dep_graph ->
      fun file_system_map ->
        fun widened ->
          let widened1 = FStar_Util.mk_ref widened in
          let uu___ = dep_graph in
          match uu___ with
          | Deps dg ->
              let uu___1 = deps_empty () in
              (match uu___1 with
               | Deps dg' ->
                   let widen_one deps1 =
                     FStar_All.pipe_right deps1
                       (FStar_List.map
                          (fun d ->
                             match d with
                             | PreferInterface m when
                                 (FStar_List.contains m friends) &&
                                   (has_implementation file_system_map m)
                                 ->
                                 (FStar_ST.op_Colon_Equals widened1 true;
                                  FriendImplementation m)
                             | uu___2 -> d)) in
                   (FStar_Util.smap_fold dg
                      (fun filename ->
                         fun dep_node1 ->
                           fun uu___3 ->
                             let uu___4 =
                               let uu___5 = dep_node1 in
                               let uu___6 = widen_one dep_node1.edges in
                               { edges = uu___6; color = White } in
                             FStar_Util.smap_add dg' filename uu___4) ();
                    (let uu___3 = FStar_ST.op_Bang widened1 in
                     (uu___3, (Deps dg')))))
let (topological_dependences_of' :
  files_for_module_name ->
    dependence_graph ->
      Prims.string Prims.list ->
        file_name Prims.list ->
          Prims.bool -> (file_name Prims.list * Prims.bool))
  =
  fun file_system_map ->
    fun dep_graph ->
      fun interfaces_needing_inlining ->
        fun root_files ->
          fun widened ->
            let rec all_friend_deps_1 dep_graph1 cycle uu___ filename =
              match uu___ with
              | (all_friends, all_files) ->
                  let dep_node1 =
                    let uu___1 = deps_try_find dep_graph1 filename in
                    FStar_Util.must uu___1 in
                  (match dep_node1.color with
                   | Gray ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black -> (all_friends, all_files)
                   | White ->
                       ((let uu___2 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep") in
                         if uu___2
                         then
                           let uu___3 =
                             let uu___4 =
                               FStar_List.map dep_to_string dep_node1.edges in
                             FStar_String.concat ", " uu___4 in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu___3
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___3 = dep_node1 in
                           { edges = (uu___3.edges); color = Gray });
                        (let uu___3 =
                           let uu___4 =
                             dependences_of file_system_map dep_graph1
                               root_files filename in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu___4 in
                         match uu___3 with
                         | (all_friends1, all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___5 = dep_node1 in
                                 { edges = (uu___5.edges); color = Black });
                              (let uu___6 =
                                 FStar_Options.debug_at_level_no_module
                                   (FStar_Options.Other "Dep") in
                               if uu___6
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu___6 =
                                 let uu___7 =
                                   FStar_List.collect
                                     (fun uu___8 ->
                                        match uu___8 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node1.edges in
                                 FStar_List.append uu___7 all_friends1 in
                               (uu___6, (filename :: all_files1)))))))
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1 ->
                   fun k ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames in
            let uu___ = all_friend_deps dep_graph [] ([], []) root_files in
            match uu___ with
            | (friends, all_files_0) ->
                ((let uu___2 =
                    FStar_Options.debug_at_level_no_module
                      (FStar_Options.Other "Dep") in
                  if uu___2
                  then
                    let uu___3 =
                      let uu___4 =
                        FStar_Util.remove_dups (fun x -> fun y -> x = y)
                          friends in
                      FStar_String.concat ", " uu___4 in
                    FStar_Util.print3
                      "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                      (FStar_String.concat ", " all_files_0) uu___3
                      (FStar_String.concat ", " interfaces_needing_inlining)
                  else ());
                 (let uu___2 =
                    widen_deps friends dep_graph file_system_map widened in
                  match uu___2 with
                  | (widened1, dep_graph1) ->
                      let uu___3 =
                        (let uu___5 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep") in
                         if uu___5
                         then
                           FStar_Util.print_string
                             "==============Phase2==================\n"
                         else ());
                        all_friend_deps dep_graph1 [] ([], []) root_files in
                      (match uu___3 with
                       | (uu___4, all_files) ->
                           ((let uu___6 =
                               FStar_Options.debug_at_level_no_module
                                 (FStar_Options.Other "Dep") in
                             if uu___6
                             then
                               FStar_Util.print1
                                 "Phase2 complete: all_files = %s\n"
                                 (FStar_String.concat ", " all_files)
                             else ());
                            (all_files, widened1)))))
let (phase1 :
  files_for_module_name ->
    dependence_graph ->
      module_name Prims.list -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun file_system_map ->
    fun dep_graph ->
      fun interfaces_needing_inlining ->
        fun for_extraction ->
          (let uu___1 =
             FStar_Options.debug_at_level_no_module
               (FStar_Options.Other "Dep") in
           if uu___1
           then
             FStar_Util.print_string
               "==============Phase1==================\n"
           else ());
          (let widened = false in
           let uu___1 = (FStar_Options.cmi ()) && for_extraction in
           if uu___1
           then
             widen_deps interfaces_needing_inlining dep_graph file_system_map
               widened
           else (widened, dep_graph))
let (topological_dependences_of :
  files_for_module_name ->
    dependence_graph ->
      Prims.string Prims.list ->
        file_name Prims.list ->
          Prims.bool -> (file_name Prims.list * Prims.bool))
  =
  fun file_system_map ->
    fun dep_graph ->
      fun interfaces_needing_inlining ->
        fun root_files ->
          fun for_extraction ->
            let uu___ =
              phase1 file_system_map dep_graph interfaces_needing_inlining
                for_extraction in
            match uu___ with
            | (widened, dep_graph1) ->
                topological_dependences_of' file_system_map dep_graph1
                  interfaces_needing_inlining root_files widened
let (collect :
  Prims.string Prims.list ->
    (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
      (Prims.string Prims.list * deps))
  =
  fun all_cmd_line_files ->
    fun get_parsing_data_from_cache ->
      let all_cmd_line_files1 =
        FStar_All.pipe_right all_cmd_line_files
          (FStar_List.map
             (fun fn ->
                let uu___ = FStar_Options.find_file fn in
                match uu___ with
                | FStar_Pervasives_Native.None ->
                    let uu___1 =
                      let uu___2 =
                        FStar_Util.format1 "File %s could not be found\n" fn in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu___2) in
                    FStar_Errors.raise_err uu___1
                | FStar_Pervasives_Native.Some fn1 -> fn1)) in
      let dep_graph = deps_empty () in
      let file_system_map = build_map all_cmd_line_files1 in
      let interfaces_needing_inlining = FStar_Util.mk_ref [] in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l in
        let uu___ =
          let uu___1 = FStar_ST.op_Bang interfaces_needing_inlining in l1 ::
            uu___1 in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu___ in
      let parse_results = FStar_Util.smap_create (Prims.of_int (40)) in
      let rec discover_one file_name1 =
        let uu___ =
          let uu___1 = deps_try_find dep_graph file_name1 in
          uu___1 = FStar_Pervasives_Native.None in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_ST.op_Bang collect_one_cache in
              FStar_Util.smap_try_find uu___3 file_name1 in
            match uu___2 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None ->
                let uu___3 =
                  collect_one file_system_map file_name1
                    get_parsing_data_from_cache in
                (match uu___3 with
                 | (parsing_data1, deps1, needs_interface_inlining,
                    additional_roots) ->
                     (parsing_data1,
                       (deps1, additional_roots, needs_interface_inlining))) in
          match uu___1 with
          | (parsing_data1, (deps1, mo_roots, needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name1
               else ();
               FStar_Util.smap_add parse_results file_name1 parsing_data1;
               (let deps2 =
                  let module_name1 = lowercase_module_name file_name1 in
                  let uu___4 =
                    (is_implementation file_name1) &&
                      (has_interface file_system_map module_name1) in
                  if uu___4
                  then FStar_List.append deps1 [UseInterface module_name1]
                  else deps1 in
                let dep_node1 =
                  let uu___4 = FStar_List.unique deps2 in
                  { edges = uu___4; color = White } in
                deps_add_dep dep_graph file_name1 dep_node1;
                (let uu___5 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps2 mo_roots) in
                 FStar_List.iter discover_one uu___5)))
        else () in
      profile
        (fun uu___1 -> FStar_List.iter discover_one all_cmd_line_files1)
        "FStar.Parser.Dep.discover";
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu___4 =
            let uu___5 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename in
            (FStar_Errors.Fatal_CyclicDependence, uu___5) in
          FStar_Errors.raise_err uu___4) in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph in
         let mo_files = FStar_Util.mk_ref [] in
         let rec aux cycle filename =
           let node =
             let uu___1 = deps_try_find dep_graph1 filename in
             match uu___1 with
             | FStar_Pervasives_Native.Some node1 -> node1
             | FStar_Pervasives_Native.None ->
                 let uu___2 =
                   FStar_Util.format1
                     "Impossible: Failed to find dependencies of %s" filename in
                 failwith uu___2 in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x ->
                     match x with
                     | UseInterface f ->
                         let uu___1 =
                           implementation_of_internal file_system_map1 f in
                         (match uu___1 with
                          | FStar_Pervasives_Native.None -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu___2 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu___1 =
                           implementation_of_internal file_system_map1 f in
                         (match uu___1 with
                          | FStar_Pervasives_Native.None -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu___2 -> [x; UseImplementation f])
                     | uu___1 -> [x])) in
           match node.color with
           | Gray -> cycle_detected dep_graph1 cycle filename
           | Black -> ()
           | White ->
               (deps_add_dep dep_graph1 filename
                  (let uu___2 = node in { edges = direct_deps; color = Gray });
                (let uu___3 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename in
                 FStar_List.iter (fun k -> aux (k :: cycle) k) uu___3);
                deps_add_dep dep_graph1 filename
                  (let uu___4 = node in
                   { edges = direct_deps; color = Black });
                (let uu___4 = is_interface filename in
                 if uu___4
                 then
                   let uu___5 =
                     let uu___6 = lowercase_module_name filename in
                     implementation_of_internal file_system_map1 uu___6 in
                   FStar_Util.iter_opt uu___5
                     (fun impl ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu___6 =
                            let uu___7 = FStar_ST.op_Bang mo_files in impl ::
                              uu___7 in
                          FStar_ST.op_Colon_Equals mo_files uu___6
                        else ())
                 else ())) in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu___2 = FStar_ST.op_Bang mo_files in
          FStar_List.iter (aux []) uu___2) in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f ->
               let m = lowercase_module_name f in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining in
        let uu___3 =
          profile
            (fun uu___4 ->
               let uu___5 =
                 let uu___6 = FStar_Options.codegen () in
                 uu___6 <> FStar_Pervasives_Native.None in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu___5)
            "FStar.Parser.Dep.topological_dependences_of" in
        match uu___3 with
        | (all_files, uu___4) ->
            ((let uu___6 =
                FStar_Options.debug_at_level_no_module
                  (FStar_Options.Other "Dep") in
              if uu___6
              then
                FStar_Util.print1 "Interfaces needing inlining: %s\n"
                  (FStar_String.concat ", " inlining_ifaces)
              else ());
             (all_files,
               (mk_deps dep_graph file_system_map all_cmd_line_files1
                  all_files inlining_ifaces parse_results)))))
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun deps1 ->
    fun f ->
      dependences_of deps1.file_system_map deps1.dep_graph
        deps1.cmd_line_files f
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig ->
    let uu___ =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu___1 ->
              match uu___1 with
              | (m, d) ->
                  let uu___2 = FStar_Util.base64_encode d in
                  FStar_Util.format2 "%s:%s" m uu___2)) in
    FStar_All.pipe_right uu___ (FStar_String.concat "\n")
let (print_make : deps -> unit) =
  fun deps1 ->
    let file_system_map = deps1.file_system_map in
    let all_cmd_line_files = deps1.cmd_line_files in
    let deps2 = deps1.dep_graph in
    let keys = deps_keys deps2 in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun f ->
            let dep_node1 =
              let uu___ = deps_try_find deps2 f in
              FStar_All.pipe_right uu___ FStar_Option.get in
            let files =
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                dep_node1.edges in
            let files1 =
              FStar_List.map (fun s -> FStar_Util.replace_chars s 32 "\\ ")
                files in
            FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))
let (print_raw : deps -> unit) =
  fun deps1 ->
    let uu___ = deps1.dep_graph in
    match uu___ with
    | Deps deps2 ->
        let uu___1 =
          let uu___2 =
            FStar_Util.smap_fold deps2
              (fun k ->
                 fun dep_node1 ->
                   fun out ->
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStar_List.map dep_to_string dep_node1.edges in
                         FStar_All.pipe_right uu___5
                           (FStar_String.concat ";\n\t") in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu___4 in
                     uu___3 :: out) [] in
          FStar_All.pipe_right uu___2 (FStar_String.concat ";;\n") in
        FStar_All.pipe_right uu___1 FStar_Util.print_endline
let (print_full : deps -> unit) =
  fun deps1 ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref [] in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map in
      let visited_other_modules = FStar_Util.smap_create (Prims.of_int (41)) in
      let should_visit lc_module_name =
        (let uu___ =
           FStar_Util.smap_try_find remaining_output_files lc_module_name in
         FStar_Option.isSome uu___) ||
          (let uu___ =
             FStar_Util.smap_try_find visited_other_modules lc_module_name in
           FStar_Option.isNone uu___) in
      let mark_visiting lc_module_name =
        let ml_file_opt =
          FStar_Util.smap_try_find remaining_output_files lc_module_name in
        FStar_Util.smap_remove remaining_output_files lc_module_name;
        FStar_Util.smap_add visited_other_modules lc_module_name true;
        ml_file_opt in
      let emit_output_file_opt ml_file_opt =
        match ml_file_opt with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some ml_file ->
            let uu___ =
              let uu___1 = FStar_ST.op_Bang order in ml_file :: uu___1 in
            FStar_ST.op_Colon_Equals order uu___ in
      let rec aux uu___ =
        match uu___ with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some file_name1 ->
                  let uu___1 = deps_try_find deps1.dep_graph file_name1 in
                  (match uu___1 with
                   | FStar_Pervasives_Native.None ->
                       let uu___2 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name1 in
                       failwith uu___2
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu___2;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps in
                       aux immediate_deps1) in
            ((let uu___2 = should_visit lc_module_name in
              if uu___2
              then
                let ml_file_opt = mark_visiting lc_module_name in
                ((let uu___4 = implementation_of deps1 lc_module_name in
                  visit_file uu___4);
                 (let uu___5 = interface_of deps1 lc_module_name in
                  visit_file uu___5);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract) in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map in
      aux all_extracted_modules;
      (let uu___1 = FStar_ST.op_Bang order in FStar_List.rev uu___1) in
    let sb =
      let uu___ = FStar_BigInt.of_int_fs (Prims.of_int (10000)) in
      FStar_StringBuffer.create uu___ in
    let pr str =
      let uu___ = FStar_StringBuffer.add str sb in
      FStar_All.pipe_left (fun uu___1 -> ()) uu___ in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n" in
    let keys = deps_keys deps1.dep_graph in
    let output_file ext fst_file =
      let ml_base_name =
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Util.basename fst_file in
            check_and_strip_suffix uu___2 in
          FStar_Option.get uu___1 in
        FStar_Util.replace_chars uu___ 46 "_" in
      let uu___ = FStar_String.op_Hat ml_base_name ext in
      FStar_Options.prepend_output_dir uu___ in
    let norm_path s =
      FStar_Util.replace_chars (FStar_Util.replace_chars s 92 "/") 32 "\\ " in
    let output_ml_file f = let uu___ = output_file ".ml" f in norm_path uu___ in
    let output_krml_file f =
      let uu___ = output_file ".krml" f in norm_path uu___ in
    let output_cmx_file f =
      let uu___ = output_file ".cmx" f in norm_path uu___ in
    let cache_file f = let uu___ = cache_file_name f in norm_path uu___ in
    let uu___ =
      phase1 deps1.file_system_map deps1.dep_graph
        deps1.interfaces_with_inlining true in
    match uu___ with
    | (widened, dep_graph) ->
        let all_checked_files =
          FStar_All.pipe_right keys
            (FStar_List.fold_left
               (fun all_checked_files1 ->
                  fun file_name1 ->
                    let process_one_key uu___1 =
                      let dep_node1 =
                        let uu___2 = deps_try_find deps1.dep_graph file_name1 in
                        FStar_All.pipe_right uu___2 FStar_Option.get in
                      let uu___2 =
                        let uu___3 = is_interface file_name1 in
                        if uu___3
                        then
                          (FStar_Pervasives_Native.None,
                            FStar_Pervasives_Native.None)
                        else
                          (let uu___5 =
                             let uu___6 = lowercase_module_name file_name1 in
                             interface_of deps1 uu___6 in
                           match uu___5 with
                           | FStar_Pervasives_Native.None ->
                               (FStar_Pervasives_Native.None,
                                 FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.Some iface ->
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       deps_try_find deps1.dep_graph iface in
                                     FStar_Option.get uu___9 in
                                   uu___8.edges in
                                 FStar_Pervasives_Native.Some uu___7 in
                               ((FStar_Pervasives_Native.Some iface), uu___6)) in
                      match uu___2 with
                      | (iface_fn, iface_deps) ->
                          let iface_deps1 =
                            FStar_Util.map_opt iface_deps
                              (FStar_List.filter
                                 (fun iface_dep ->
                                    let uu___3 =
                                      FStar_Util.for_some
                                        (dep_subsumed_by iface_dep)
                                        dep_node1.edges in
                                    Prims.op_Negation uu___3)) in
                          let norm_f = norm_path file_name1 in
                          let files =
                            FStar_List.map
                              (file_of_dep_aux true deps1.file_system_map
                                 deps1.cmd_line_files) dep_node1.edges in
                          let files1 =
                            match iface_deps1 with
                            | FStar_Pervasives_Native.None -> files
                            | FStar_Pervasives_Native.Some iface_deps2 ->
                                let iface_files =
                                  FStar_List.map
                                    (file_of_dep_aux true
                                       deps1.file_system_map
                                       deps1.cmd_line_files) iface_deps2 in
                                FStar_Util.remove_dups
                                  (fun x -> fun y -> x = y)
                                  (FStar_List.append files iface_files) in
                          let files2 =
                            let uu___3 =
                              FStar_All.pipe_right iface_fn
                                FStar_Util.is_some in
                            if uu___3
                            then
                              let iface_fn1 =
                                FStar_All.pipe_right iface_fn FStar_Util.must in
                              let uu___4 =
                                FStar_All.pipe_right files1
                                  (FStar_List.filter
                                     (fun f -> f <> iface_fn1)) in
                              FStar_All.pipe_right uu___4
                                (fun files3 ->
                                   let uu___5 = cache_file_name iface_fn1 in
                                   uu___5 :: files3)
                            else files1 in
                          let files3 = FStar_List.map norm_path files2 in
                          let files4 = FStar_String.concat "\\\n\t" files3 in
                          let cache_file_name1 = cache_file file_name1 in
                          let all_checked_files2 =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 = module_name_of_file file_name1 in
                                FStar_Options.should_be_already_cached uu___5 in
                              Prims.op_Negation uu___4 in
                            if uu___3
                            then
                              (print_entry cache_file_name1 norm_f files4;
                               cache_file_name1
                               ::
                               all_checked_files1)
                            else all_checked_files1 in
                          let uu___3 =
                            let uu___4 = FStar_Options.cmi () in
                            if uu___4
                            then
                              profile
                                (fun uu___5 ->
                                   let uu___6 = dep_graph_copy dep_graph in
                                   topological_dependences_of'
                                     deps1.file_system_map uu___6
                                     deps1.interfaces_with_inlining
                                     [file_name1] widened)
                                "FStar.Parser.Dep.topological_dependences_of_2"
                            else
                              (let maybe_widen_deps f_deps =
                                 FStar_List.map
                                   (fun dep ->
                                      file_of_dep_aux false
                                        deps1.file_system_map
                                        deps1.cmd_line_files dep) f_deps in
                               let fst_files =
                                 maybe_widen_deps dep_node1.edges in
                               let fst_files_from_iface =
                                 match iface_deps1 with
                                 | FStar_Pervasives_Native.None -> []
                                 | FStar_Pervasives_Native.Some iface_deps2
                                     -> maybe_widen_deps iface_deps2 in
                               let uu___6 =
                                 FStar_Util.remove_dups
                                   (fun x -> fun y -> x = y)
                                   (FStar_List.append fst_files
                                      fst_files_from_iface) in
                               (uu___6, false)) in
                          (match uu___3 with
                           | (all_fst_files_dep, widened1) ->
                               let all_checked_fst_dep_files =
                                 FStar_All.pipe_right all_fst_files_dep
                                   (FStar_List.map cache_file) in
                               let all_checked_fst_dep_files_string =
                                 FStar_String.concat " \\\n\t"
                                   all_checked_fst_dep_files in
                               ((let uu___5 = is_implementation file_name1 in
                                 if uu___5
                                 then
                                   ((let uu___7 =
                                       (FStar_Options.cmi ()) && widened1 in
                                     if uu___7
                                     then
                                       ((let uu___9 =
                                           output_ml_file file_name1 in
                                         print_entry uu___9 cache_file_name1
                                           all_checked_fst_dep_files_string);
                                        (let uu___9 =
                                           output_krml_file file_name1 in
                                         print_entry uu___9 cache_file_name1
                                           all_checked_fst_dep_files_string))
                                     else
                                       ((let uu___10 =
                                           output_ml_file file_name1 in
                                         print_entry uu___10 cache_file_name1
                                           "");
                                        (let uu___10 =
                                           output_krml_file file_name1 in
                                         print_entry uu___10 cache_file_name1
                                           "")));
                                    (let cmx_files =
                                       let extracted_fst_files =
                                         FStar_All.pipe_right
                                           all_fst_files_dep
                                           (FStar_List.filter
                                              (fun df ->
                                                 (let uu___7 =
                                                    lowercase_module_name df in
                                                  let uu___8 =
                                                    lowercase_module_name
                                                      file_name1 in
                                                  uu___7 <> uu___8) &&
                                                   (let uu___7 =
                                                      lowercase_module_name
                                                        df in
                                                    FStar_Options.should_extract
                                                      uu___7))) in
                                       FStar_All.pipe_right
                                         extracted_fst_files
                                         (FStar_List.map output_cmx_file) in
                                     let uu___7 =
                                       let uu___8 =
                                         lowercase_module_name file_name1 in
                                       FStar_Options.should_extract uu___8 in
                                     if uu___7
                                     then
                                       let cmx_files1 =
                                         FStar_String.concat "\\\n\t"
                                           cmx_files in
                                       let uu___8 =
                                         output_cmx_file file_name1 in
                                       let uu___9 = output_ml_file file_name1 in
                                       print_entry uu___8 uu___9 cmx_files1
                                     else ()))
                                 else
                                   (let uu___7 =
                                      (let uu___8 =
                                         let uu___9 =
                                           lowercase_module_name file_name1 in
                                         has_implementation
                                           deps1.file_system_map uu___9 in
                                       Prims.op_Negation uu___8) &&
                                        (is_interface file_name1) in
                                    if uu___7
                                    then
                                      let uu___8 =
                                        (FStar_Options.cmi ()) &&
                                          (widened1 || true) in
                                      (if uu___8
                                       then
                                         let uu___9 =
                                           output_krml_file file_name1 in
                                         print_entry uu___9 cache_file_name1
                                           all_checked_fst_dep_files_string
                                       else
                                         (let uu___10 =
                                            output_krml_file file_name1 in
                                          print_entry uu___10
                                            cache_file_name1 ""))
                                    else ()));
                                all_checked_files2)) in
                    profile process_one_key
                      "FStar.Parser.Dep.process_one_key") []) in
        let all_fst_files =
          let uu___1 =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
          FStar_All.pipe_right uu___1
            (FStar_Util.sort_with FStar_String.compare) in
        let all_fsti_files =
          let uu___1 =
            FStar_All.pipe_right keys (FStar_List.filter is_interface) in
          FStar_All.pipe_right uu___1
            (FStar_Util.sort_with FStar_String.compare) in
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.of_int (41)) in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file ->
                  let mname = lowercase_module_name fst_file in
                  let uu___2 = FStar_Options.should_extract mname in
                  if uu___2
                  then
                    let uu___3 = output_ml_file fst_file in
                    FStar_Util.smap_add ml_file_map mname uu___3
                  else ()));
          sort_output_files ml_file_map in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.of_int (41)) in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file ->
                  let mname = lowercase_module_name fst_file in
                  let uu___2 = output_krml_file fst_file in
                  FStar_Util.smap_add krml_file_map mname uu___2));
          sort_output_files krml_file_map in
        let print_all tag files =
          pr tag;
          pr "=\\\n\t";
          FStar_List.iter (fun f -> pr (norm_path f); pr " \\\n\t") files;
          pr "\n" in
        (FStar_All.pipe_right all_fsti_files
           (FStar_List.iter
              (fun fsti ->
                 let mn = lowercase_module_name fsti in
                 let range_of_file fsti1 =
                   let r =
                     FStar_Range.set_file_of_range FStar_Range.dummyRange
                       fsti1 in
                   let uu___2 = FStar_Range.def_range r in
                   FStar_Range.set_use_range r uu___2 in
                 let uu___2 =
                   let uu___3 = has_implementation deps1.file_system_map mn in
                   Prims.op_Negation uu___3 in
                 if uu___2
                 then
                   let uu___3 = range_of_file fsti in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = module_name_of_file fsti in
                       FStar_Util.format1
                         "Interface %s is admitted without an implementation"
                         uu___6 in
                     (FStar_Errors.Warning_WarnOnUse, uu___5) in
                   FStar_Errors.log_issue uu___3 uu___4
                 else ()));
         print_all "ALL_FST_FILES" all_fst_files;
         print_all "ALL_FSTI_FILES" all_fsti_files;
         print_all "ALL_CHECKED_FILES" all_checked_files;
         print_all "ALL_ML_FILES" all_ml_files;
         print_all "ALL_KRML_FILES" all_krml_files;
         FStar_StringBuffer.output_channel FStar_Util.stdout sb)
let (print : deps -> unit) =
  fun deps1 ->
    let uu___ = FStar_Options.dep () in
    match uu___ with
    | FStar_Pervasives_Native.Some "make" -> print_make deps1
    | FStar_Pervasives_Native.Some "full" ->
        profile (fun uu___1 -> print_full deps1)
          "FStar.Parser.Deps.print_full_deps"
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps1.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps1
    | FStar_Pervasives_Native.Some uu___1 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None -> ()
let (print_fsmap :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap -> Prims.string)
  =
  fun fsmap ->
    FStar_Util.smap_fold fsmap
      (fun k ->
         fun uu___ ->
           fun s ->
             match uu___ with
             | (v0, v1) ->
                 let uu___1 =
                   let uu___2 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1) in
                   FStar_String.op_Hat "; " uu___2 in
                 FStar_String.op_Hat s uu___1) ""
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps1 ->
    fun module_name1 ->
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid module_name1 in
        FStar_String.lowercase uu___1 in
      has_interface deps1.file_system_map uu___
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps1 ->
    fun module_name1 ->
      let m =
        let uu___ = FStar_Ident.string_of_lid module_name1 in
        FStar_String.lowercase uu___ in
      FStar_All.pipe_right deps1.all_files
        (FStar_Util.for_some
           (fun f ->
              (is_implementation f) &&
                (let uu___ =
                   let uu___1 = module_name_of_file f in
                   FStar_String.lowercase uu___1 in
                 uu___ = m)))