open Prims
let profile : 'uuuuuu16 . (unit -> 'uuuuuu16) -> Prims.string -> 'uuuuuu16 =
  fun f -> fun c -> FStar_Profiling.profile f FStar_Pervasives_Native.None c
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyAll -> true | uu____37 -> false
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyUserList -> true | uu____43 -> false
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyFigureItOut -> true | uu____49 -> false
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee -> match projectee with | White -> true | uu____65 -> false
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee -> match projectee with | Gray -> true | uu____71 -> false
let (uu___is_Black : color -> Prims.bool) =
  fun projectee -> match projectee with | Black -> true | uu____77 -> false
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu____83 -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu____89 -> false
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____117 =
             (l > lext) &&
               (let uu____119 = FStar_String.substring f (l - lext) lext in
                uu____119 = ext) in
           if uu____117
           then
             let uu____122 =
               FStar_String.substring f Prims.int_zero (l - lext) in
             FStar_Pervasives_Native.Some uu____122
           else FStar_Pervasives_Native.None) suffixes in
    let uu____124 = FStar_List.filter FStar_Util.is_some matches in
    match uu____124 with
    | (FStar_Pervasives_Native.Some m)::uu____134 ->
        FStar_Pervasives_Native.Some m
    | uu____141 -> FStar_Pervasives_Native.None
let (is_interface : Prims.string -> Prims.bool) =
  fun f ->
    let uu____151 =
      FStar_String.get f ((FStar_String.length f) - Prims.int_one) in
    uu____151 = 105
let (is_implementation : Prims.string -> Prims.bool) =
  fun f -> let uu____157 = is_interface f in Prims.op_Negation uu____157
let list_of_option :
  'uuuuuu162 .
    'uuuuuu162 FStar_Pervasives_Native.option -> 'uuuuuu162 Prims.list
  =
  fun uu___0_171 ->
    match uu___0_171 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None -> []
let list_of_pair :
  'uuuuuu179 .
    ('uuuuuu179 FStar_Pervasives_Native.option * 'uuuuuu179
      FStar_Pervasives_Native.option) -> 'uuuuuu179 Prims.list
  =
  fun uu____194 ->
    match uu____194 with
    | (intf, impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f ->
    let uu____218 =
      let uu____221 = FStar_Util.basename f in
      check_and_strip_suffix uu____221 in
    match uu____218 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None ->
        let uu____223 =
          let uu____228 = FStar_Util.format1 "not a valid FStar file: %s" f in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____228) in
        FStar_Errors.raise_err uu____223
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f ->
    let uu____234 = module_name_of_file f in FStar_String.lowercase uu____234
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f ->
    let lid =
      let uu____243 = FStar_Ident.path_of_text f in
      FStar_Ident.lid_of_path uu____243 FStar_Range.dummyRange in
    let uu____244 = FStar_Ident.ns_of_lid lid in
    match uu____244 with
    | [] -> FStar_Pervasives_Native.None
    | ns ->
        let uu____248 = FStar_Ident.lid_of_ids ns in
        FStar_Pervasives_Native.Some uu____248
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | UseInterface _0 -> true | uu____275 -> false
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | UseInterface _0 -> _0
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | PreferInterface _0 -> true | uu____288 -> false
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | PreferInterface _0 -> _0
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | UseImplementation _0 -> true | uu____301 -> false
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | UseImplementation _0 -> _0
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____314 -> false
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | FriendImplementation _0 -> _0
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_325 ->
    match uu___1_325 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
type dependences = dependence Prims.list
let empty_dependences : 'uuuuuu334 . unit -> 'uuuuuu334 Prims.list =
  fun uu____338 -> []
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
  | P_open_module_or_namespace of (open_kind * FStar_Ident.lid) 
  | P_dep of (Prims.bool * FStar_Ident.lident) 
  | P_alias of (FStar_Ident.ident * FStar_Ident.lident) 
  | P_lid of FStar_Ident.lident 
  | P_inline_for_extraction 
let (uu___is_P_begin_module : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_begin_module _0 -> true | uu____439 -> false
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee -> match projectee with | P_begin_module _0 -> _0
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_open _0 -> true | uu____456 -> false
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee -> match projectee with | P_open _0 -> _0
let (uu___is_P_open_module_or_namespace : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with
    | P_open_module_or_namespace _0 -> true
    | uu____485 -> false
let (__proj__P_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStar_Ident.lid)) =
  fun projectee -> match projectee with | P_open_module_or_namespace _0 -> _0
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_dep _0 -> true | uu____514 -> false
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee -> match projectee with | P_dep _0 -> _0
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_alias _0 -> true | uu____543 -> false
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee -> match projectee with | P_alias _0 -> _0
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_lid _0 -> true | uu____568 -> false
let (__proj__P_lid__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee -> match projectee with | P_lid _0 -> _0
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with
    | P_inline_for_extraction -> true
    | uu____580 -> false
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee -> true
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee -> match projectee with | Mk_pd _0 -> _0
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt ->
    let str_of_open_kind uu___2_615 =
      match uu___2_615 with
      | Open_module -> "P_open_module"
      | Open_namespace -> "P_open_namespace" in
    match elt with
    | P_begin_module lid ->
        let uu____617 =
          let uu____618 = FStar_Ident.string_of_lid lid in
          FStar_String.op_Hat uu____618 ")" in
        FStar_String.op_Hat "P_begin_module (" uu____617
    | P_open (b, lid) ->
        let uu____621 =
          let uu____622 = FStar_Util.string_of_bool b in
          let uu____623 =
            let uu____624 =
              let uu____625 = FStar_Ident.string_of_lid lid in
              FStar_String.op_Hat uu____625 ")" in
            FStar_String.op_Hat ", " uu____624 in
          FStar_String.op_Hat uu____622 uu____623 in
        FStar_String.op_Hat "P_open (" uu____621
    | P_open_module_or_namespace (k, lid) ->
        let uu____628 =
          let uu____629 =
            let uu____630 =
              let uu____631 = FStar_Ident.string_of_lid lid in
              FStar_String.op_Hat uu____631 ")" in
            FStar_String.op_Hat ", " uu____630 in
          FStar_String.op_Hat (str_of_open_kind k) uu____629 in
        FStar_String.op_Hat "P_open_module_or_namespace (" uu____628
    | P_dep (b, lid) ->
        let uu____634 =
          let uu____635 = FStar_Ident.string_of_lid lid in
          let uu____636 =
            let uu____637 =
              let uu____638 = FStar_Util.string_of_bool b in
              FStar_String.op_Hat uu____638 ")" in
            FStar_String.op_Hat ", " uu____637 in
          FStar_String.op_Hat uu____635 uu____636 in
        FStar_String.op_Hat "P_dep (" uu____634
    | P_alias (id, lid) ->
        let uu____641 =
          let uu____642 = FStar_Ident.string_of_id id in
          let uu____643 =
            let uu____644 =
              let uu____645 = FStar_Ident.string_of_lid lid in
              FStar_String.op_Hat uu____645 ")" in
            FStar_String.op_Hat ", " uu____644 in
          FStar_String.op_Hat uu____642 uu____643 in
        FStar_String.op_Hat "P_alias (" uu____641
    | P_lid lid ->
        let uu____647 =
          let uu____648 = FStar_Ident.string_of_lid lid in
          FStar_String.op_Hat uu____648 ")" in
        FStar_String.op_Hat "P_lid (" uu____647
    | P_inline_for_extraction -> "P_inline_for_extraction"
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___3_653 ->
    match uu___3_653 with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s ->
                fun elt ->
                  let uu____664 =
                    let uu____665 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt in
                    FStar_String.op_Hat "; " uu____665 in
                  FStar_String.op_Hat s uu____664) "")
let (parsing_data_elt_eq :
  parsing_data_elt -> parsing_data_elt -> Prims.bool) =
  fun e1 ->
    fun e2 ->
      match (e1, e2) with
      | (P_begin_module l1, P_begin_module l2) ->
          FStar_Ident.lid_equals l1 l2
      | (P_open (b1, l1), P_open (b2, l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_open_module_or_namespace (k1, l1), P_open_module_or_namespace
         (k2, l2)) -> (k1 = k2) && (FStar_Ident.lid_equals l1 l2)
      | (P_dep (b1, l1), P_dep (b2, l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_alias (i1, l1), P_alias (i2, l2)) ->
          (let uu____698 = FStar_Ident.string_of_id i1 in
           let uu____699 = FStar_Ident.string_of_id i2 in
           uu____698 = uu____699) && (FStar_Ident.lid_equals l1 l2)
      | (P_lid l1, P_lid l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction, P_inline_for_extraction) -> true
      | (uu____702, uu____703) -> false
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
  fun uu____882 ->
    fun k -> match uu____882 with | Deps m -> FStar_Util.smap_try_find m k
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____901 ->
    fun k ->
      fun v -> match uu____901 with | Deps m -> FStar_Util.smap_add m k v
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____913 -> match uu____913 with | Deps m -> FStar_Util.smap_keys m
let (deps_empty : unit -> dependence_graph) =
  fun uu____923 ->
    let uu____924 = FStar_Util.smap_create (Prims.of_int (41)) in
    Deps uu____924
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
  let uu____973 = deps_empty () in
  let uu____974 = FStar_Util.smap_create Prims.int_zero in
  let uu____983 = FStar_Util.smap_create Prims.int_zero in
  mk_deps uu____973 uu____974 [] [] [] uu____983
let (module_name_of_dep : dependence -> module_name) =
  fun uu___4_990 ->
    match uu___4_990 with
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
      let uu____1009 = FStar_Util.smap_try_find file_system_map key in
      match uu____1009 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn, uu____1031) ->
          let uu____1046 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____1046
      | FStar_Pervasives_Native.Some
          (uu____1047, FStar_Pervasives_Native.Some fn) ->
          let uu____1063 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____1063
      | uu____1064 -> FStar_Pervasives_Native.None
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu____1089 = FStar_Util.smap_try_find file_system_map key in
      match uu____1089 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface, uu____1111) ->
          FStar_Pervasives_Native.Some iface
      | uu____1126 -> FStar_Pervasives_Native.None
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu____1151 = FStar_Util.smap_try_find file_system_map key in
      match uu____1151 with
      | FStar_Pervasives_Native.Some
          (uu____1172, FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1188 -> FStar_Pervasives_Native.None
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
      let uu____1233 = interface_of_internal file_system_map key in
      FStar_Option.isSome uu____1233
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map ->
    fun key ->
      let uu____1246 = implementation_of_internal file_system_map key in
      FStar_Option.isSome uu____1246
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax = FStar_Options.lax () in
    let cache_fn =
      if lax
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked" in
    let mname = FStar_All.pipe_right fn module_name_of_file in
    let uu____1263 =
      let uu____1266 = FStar_All.pipe_right cache_fn FStar_Util.basename in
      FStar_Options.find_file uu____1266 in
    match uu____1263 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn in
        ((let uu____1270 =
            ((let uu____1273 = FStar_Options.dep () in
              FStar_Option.isSome uu____1273) &&
               (let uu____1277 = FStar_Options.should_be_already_cached mname in
                Prims.op_Negation uu____1277))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1279 =
                    FStar_Util.paths_to_same_file path expected_cache_file in
                  Prims.op_Negation uu____1279)) in
          if uu____1270
          then
            let uu____1280 =
              let uu____1285 =
                let uu____1286 = FStar_Options.prepend_cache_dir cache_fn in
                FStar_Util.format3
                  "Did not expect %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1286 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1285) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1280
          else ());
         (let uu____1288 =
            (FStar_Util.file_exists expected_cache_file) &&
              (FStar_Util.paths_to_same_file path expected_cache_file) in
          if uu____1288 then expected_cache_file else path))
    | FStar_Pervasives_Native.None ->
        let uu____1290 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached in
        if uu____1290
        then
          let uu____1291 =
            let uu____1296 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1296) in
          FStar_Errors.raise_err uu____1291
        else FStar_Options.prepend_cache_dir cache_fn in
  let memo = FStar_Util.smap_create (Prims.of_int (100)) in
  let memo1 f x =
    let uu____1317 = FStar_Util.smap_try_find memo x in
    match uu____1317 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None ->
        let res = f x in (FStar_Util.smap_add memo x res; res) in
  memo1 checked_file_and_exists_flag
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps1 ->
    fun fn ->
      let uu____1333 = FStar_Util.smap_try_find deps1.parse_results fn in
      FStar_All.pipe_right uu____1333 FStar_Util.must
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
                      (let uu____1373 = lowercase_module_name fn in
                       key = uu____1373))) in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____1382 = interface_of_internal file_system_map key in
              (match uu____1382 with
               | FStar_Pervasives_Native.None ->
                   let uu____1386 =
                     let uu____1391 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingInterface, uu____1391) in
                   FStar_Errors.raise_err uu____1386
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1394 =
                (cmd_line_has_impl key) &&
                  (let uu____1396 = FStar_Options.dep () in
                   FStar_Option.isNone uu____1396) in
              if uu____1394
              then
                let uu____1399 = FStar_Options.expose_interfaces () in
                (if uu____1399
                 then
                   let uu____1400 =
                     let uu____1401 =
                       implementation_of_internal file_system_map key in
                     FStar_Option.get uu____1401 in
                   maybe_use_cache_of uu____1400
                 else
                   (let uu____1405 =
                      let uu____1410 =
                        let uu____1411 =
                          let uu____1412 =
                            implementation_of_internal file_system_map key in
                          FStar_Option.get uu____1412 in
                        let uu____1415 =
                          let uu____1416 =
                            interface_of_internal file_system_map key in
                          FStar_Option.get uu____1416 in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1411 uu____1415 in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1410) in
                    FStar_Errors.raise_err uu____1405))
              else
                (let uu____1420 =
                   let uu____1421 = interface_of_internal file_system_map key in
                   FStar_Option.get uu____1421 in
                 maybe_use_cache_of uu____1420)
          | PreferInterface key ->
              let uu____1425 = implementation_of_internal file_system_map key in
              (match uu____1425 with
               | FStar_Pervasives_Native.None ->
                   let uu____1428 =
                     let uu____1433 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1433) in
                   FStar_Errors.raise_err uu____1428
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____1436 = implementation_of_internal file_system_map key in
              (match uu____1436 with
               | FStar_Pervasives_Native.None ->
                   let uu____1439 =
                     let uu____1444 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1444) in
                   FStar_Errors.raise_err uu____1439
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____1447 = implementation_of_internal file_system_map key in
              (match uu____1447 with
               | FStar_Pervasives_Native.None ->
                   let uu____1450 =
                     let uu____1455 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1455) in
                   FStar_Errors.raise_err uu____1450
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
          let uu____1499 = deps_try_find deps1 fn in
          match uu____1499 with
          | FStar_Pervasives_Native.None -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps2; color = uu____1505;_} ->
              let uu____1506 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files) deps2 in
              FStar_All.pipe_right uu____1506
                (FStar_List.filter (fun k -> k <> fn))
let (print_graph : dependence_graph -> unit) =
  fun graph ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1523 =
       let uu____1524 =
         let uu____1525 =
           let uu____1526 =
             let uu____1529 =
               let uu____1532 = deps_keys graph in
               FStar_List.unique uu____1532 in
             FStar_List.collect
               (fun k ->
                  let deps1 =
                    let uu____1541 =
                      let uu____1542 = deps_try_find graph k in
                      FStar_Util.must uu____1542 in
                    uu____1541.edges in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print dep =
                    let uu____1557 =
                      let uu____1558 = lowercase_module_name k in
                      r uu____1558 in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1557
                      (r (module_name_of_dep dep)) in
                  FStar_List.map print deps1) uu____1529 in
           FStar_String.concat "\n" uu____1526 in
         FStar_String.op_Hat uu____1525 "\n}\n" in
       FStar_String.op_Hat "digraph {\n" uu____1524 in
     FStar_Util.write_file "dep.graph" uu____1523)
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____1569 ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____1586 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____1586 in
    FStar_List.concatMap
      (fun d ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f ->
                let f1 = FStar_Util.basename f in
                let uu____1612 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1612
                  (FStar_Util.map_option
                     (fun longname ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1633 =
              let uu____1638 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1638) in
            FStar_Errors.raise_err uu____1633)) include_directories2
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames ->
    let map = FStar_Util.smap_create (Prims.of_int (41)) in
    let add_entry key full_path =
      let uu____1684 = FStar_Util.smap_try_find map key in
      match uu____1684 with
      | FStar_Pervasives_Native.Some (intf, impl) ->
          let uu____1721 = is_interface full_path in
          if uu____1721
          then
            FStar_Util.smap_add map key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None ->
          let uu____1755 = is_interface full_path in
          if uu____1755
          then
            FStar_Util.smap_add map key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1782 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1796 ->
          match uu____1796 with
          | (longname, full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1782);
    FStar_List.iter
      (fun f ->
         let uu____1807 = lowercase_module_name f in add_entry uu____1807 f)
      filenames;
    map
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool)
  =
  fun original_map ->
    fun working_map ->
      fun prefix ->
        let found = FStar_Util.mk_ref false in
        let prefix1 = FStar_String.op_Hat prefix "." in
        FStar_Util.smap_iter original_map
          (fun k ->
             fun uu____1842 ->
               if FStar_Util.starts_with k prefix1
               then
                 let suffix =
                   FStar_String.substring k (FStar_String.length prefix1)
                     ((FStar_String.length k) - (FStar_String.length prefix1)) in
                 let filename =
                   let uu____1861 = FStar_Util.smap_try_find original_map k in
                   FStar_Util.must uu____1861 in
                 (FStar_Util.smap_add working_map suffix filename;
                  FStar_ST.op_Colon_Equals found true)
               else ());
        FStar_ST.op_Bang found
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l ->
    fun last ->
      let suffix =
        if last
        then
          let uu____1925 =
            let uu____1926 = FStar_Ident.ident_of_lid l in
            FStar_Ident.string_of_id uu____1926 in
          [uu____1925]
        else [] in
      let names =
        let uu____1931 =
          let uu____1934 = FStar_Ident.ns_of_lid l in
          FStar_List.map (fun x -> FStar_Ident.string_of_id x) uu____1934 in
        FStar_List.append uu____1931 suffix in
      FStar_String.concat "." names
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l ->
    fun last ->
      let uu____1949 = string_of_lid l last in
      FStar_String.lowercase uu____1949
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu____1955 =
      let uu____1958 = FStar_Ident.ns_of_lid l in
      FStar_List.map FStar_Ident.string_of_id uu____1958 in
    FStar_String.concat "_" uu____1955
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid ->
    fun filename ->
      let k' = lowercase_join_longident lid true in
      let uu____1972 =
        let uu____1973 =
          let uu____1974 =
            let uu____1975 =
              let uu____1978 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1978 in
            FStar_Util.must uu____1975 in
          FStar_String.lowercase uu____1974 in
        uu____1973 <> k' in
      if uu____1972
      then
        let uu____1979 = FStar_Ident.range_of_lid lid in
        let uu____1980 =
          let uu____1985 =
            let uu____1986 = string_of_lid lid true in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1986 filename in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1985) in
        FStar_Errors.log_issue uu____1979 uu____1980
      else ()
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____1993 -> false
let (core_modules : Prims.string Prims.list) =
  let uu____1996 =
    let uu____1999 = FStar_Options.prims_basename () in
    let uu____2000 =
      let uu____2003 = FStar_Options.pervasives_basename () in
      let uu____2004 =
        let uu____2007 = FStar_Options.pervasives_native_basename () in
        [uu____2007] in
      uu____2003 :: uu____2004 in
    uu____1999 :: uu____2000 in
  FStar_All.pipe_right uu____1996 (FStar_List.map module_name_of_file)
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename ->
    let filename = FStar_Util.basename full_filename in
    let uu____2024 =
      let uu____2025 = module_name_of_file filename in
      FStar_List.mem uu____2025 core_modules in
    if uu____2024
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)] in
       let uu____2060 =
         let uu____2063 = lowercase_module_name full_filename in
         namespace_of_module uu____2063 in
       match uu____2060 with
       | FStar_Pervasives_Native.None -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d ->
    fun d' ->
      match (d, d') with
      | (PreferInterface l', FriendImplementation l) -> l = l'
      | uu____2095 -> d = d'
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
            let uu____2198 =
              (is_interface filename1) &&
                (has_implementation original_map1 mname) in
            if uu____2198 then [UseImplementation mname] else [] in
          let auto_open =
            let uu____2205 = hard_coded_dependencies filename1 in
            FStar_All.pipe_right uu____2205
              (FStar_List.map
                 (fun uu____2227 ->
                    match uu____2227 with
                    | (lid, k) -> P_open_module_or_namespace (k, lid))) in
          let working_map = FStar_Util.smap_copy original_map1 in
          let set_interface_inlining uu____2258 =
            let uu____2259 = is_interface filename1 in
            if uu____2259
            then FStar_ST.op_Colon_Equals has_inline_for_extraction true
            else () in
          let add_dep deps2 d =
            let uu____2310 =
              let uu____2311 =
                let uu____2312 = FStar_ST.op_Bang deps2 in
                FStar_List.existsML (dep_subsumed_by d) uu____2312 in
              Prims.op_Negation uu____2311 in
            if uu____2310
            then
              let uu____2325 =
                let uu____2328 = FStar_ST.op_Bang deps2 in d :: uu____2328 in
              FStar_ST.op_Colon_Equals deps2 uu____2325
            else () in
          let dep_edge module_name1 is_friend =
            if is_friend
            then FriendImplementation module_name1
            else PreferInterface module_name1 in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true in
            let uu____2381 = resolve_module_name original_or_working_map key in
            match uu____2381 with
            | FStar_Pervasives_Native.Some module_name1 ->
                (add_dep deps1 (dep_edge module_name1 is_friend); true)
            | uu____2386 -> false in
          let record_open_module let_open lid =
            let uu____2400 =
              (let_open && (add_dependence_edge working_map lid false)) ||
                ((Prims.op_Negation let_open) &&
                   (add_dependence_edge original_map1 lid false)) in
            if uu____2400
            then true
            else
              (if let_open
               then
                 (let uu____2403 = FStar_Ident.range_of_lid lid in
                  let uu____2404 =
                    let uu____2409 =
                      let uu____2410 = string_of_lid lid true in
                      FStar_Util.format1 "Module not found: %s" uu____2410 in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____2409) in
                  FStar_Errors.log_issue uu____2403 uu____2404)
               else ();
               false) in
          let record_open_namespace lid =
            let key = lowercase_join_longident lid true in
            let r = enter_namespace original_map1 working_map key in
            if Prims.op_Negation r
            then
              let uu____2420 = FStar_Ident.range_of_lid lid in
              let uu____2421 =
                let uu____2426 =
                  let uu____2427 = string_of_lid lid true in
                  FStar_Util.format1
                    "No modules in namespace %s and no file with that name either"
                    uu____2427 in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2426) in
              FStar_Errors.log_issue uu____2420 uu____2421
            else () in
          let record_open let_open lid =
            let uu____2440 = record_open_module let_open lid in
            if uu____2440
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid
              else () in
          let record_open_module_or_namespace uu____2452 =
            match uu____2452 with
            | (lid, kind) ->
                (match kind with
                 | Open_namespace -> record_open_namespace lid
                 | Open_module ->
                     let uu____2459 = record_open_module false lid in ()) in
          let record_module_alias ident lid =
            let key =
              let uu____2472 = FStar_Ident.string_of_id ident in
              FStar_String.lowercase uu____2472 in
            let alias = lowercase_join_longident lid true in
            let uu____2474 = FStar_Util.smap_try_find original_map1 alias in
            match uu____2474 with
            | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                (FStar_Util.smap_add working_map key deps_of_aliased_module;
                 (let uu____2520 =
                    let uu____2521 = lowercase_join_longident lid true in
                    dep_edge uu____2521 false in
                  add_dep deps1 uu____2520);
                 true)
            | FStar_Pervasives_Native.None ->
                ((let uu____2531 = FStar_Ident.range_of_lid lid in
                  let uu____2532 =
                    let uu____2537 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____2537) in
                  FStar_Errors.log_issue uu____2531 uu____2532);
                 false) in
          let add_dep_on_module module_name1 is_friend =
            let uu____2549 =
              add_dependence_edge working_map module_name1 is_friend in
            if uu____2549
            then ()
            else
              (let uu____2551 =
                 FStar_Options.debug_at_level_no_module
                   (FStar_Options.Other "Dep") in
               if uu____2551
               then
                 let uu____2552 = FStar_Ident.range_of_lid module_name1 in
                 let uu____2553 =
                   let uu____2558 =
                     let uu____2559 = FStar_Ident.string_of_lid module_name1 in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2559 in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2558) in
                 FStar_Errors.log_issue uu____2552 uu____2553
               else ()) in
          let record_lid lid =
            let uu____2567 = FStar_Ident.ns_of_lid lid in
            match uu____2567 with
            | [] -> ()
            | ns ->
                let module_name1 = FStar_Ident.lid_of_ids ns in
                add_dep_on_module module_name1 false in
          let begin_module lid =
            let uu____2576 =
              let uu____2577 =
                let uu____2578 = FStar_Ident.ns_of_lid lid in
                FStar_List.length uu____2578 in
              uu____2577 > Prims.int_zero in
            if uu____2576
            then
              let uu____2581 =
                let uu____2582 = namespace_of_lid lid in
                enter_namespace original_map1 working_map uu____2582 in
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
                       | P_open_module_or_namespace (k, lid) ->
                           record_open_module_or_namespace (lid, k)
                       | P_dep (b, lid) -> add_dep_on_module lid b
                       | P_alias (id, lid) ->
                           let uu____2602 = record_module_alias id lid in ()
                       | P_lid lid -> record_lid lid
                       | P_inline_for_extraction -> set_interface_inlining ())));
          (let uu____2604 = FStar_ST.op_Bang deps1 in
           let uu____2617 = FStar_ST.op_Bang has_inline_for_extraction in
           (uu____2604, uu____2617, mo_roots)) in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache in
        let uu____2633 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some in
        if uu____2633
        then
          ((let uu____2649 =
              FStar_Options.debug_at_level_no_module
                (FStar_Options.Other "Dep") in
            if uu____2649
            then
              FStar_Util.print1
                "Reading the parsing data for %s from its checked file\n"
                filename
            else ());
           (let uu____2651 =
              let uu____2662 =
                FStar_All.pipe_right data_from_cache FStar_Util.must in
              from_parsing_data uu____2662 original_map filename in
            match uu____2651 with
            | (deps1, has_inline_for_extraction, mo_roots) ->
                let uu____2688 =
                  FStar_All.pipe_right data_from_cache FStar_Util.must in
                (uu____2688, deps1, has_inline_for_extraction, mo_roots)))
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref Prims.int_zero in
           let pd = FStar_Util.mk_ref [] in
           let add_to_parsing_data elt =
             let uu____2712 =
               let uu____2713 =
                 let uu____2714 = FStar_ST.op_Bang pd in
                 FStar_List.existsML (fun e -> parsing_data_elt_eq e elt)
                   uu____2714 in
               Prims.op_Negation uu____2713 in
             if uu____2712
             then
               let uu____2729 =
                 let uu____2732 = FStar_ST.op_Bang pd in elt :: uu____2732 in
               FStar_ST.op_Colon_Equals pd uu____2729
             else () in
           let rec collect_module uu___5_2862 =
             match uu___5_2862 with
             | FStar_Parser_AST.Module (lid, decls) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
             | FStar_Parser_AST.Interface (lid, decls, uu____2873) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
           and collect_decls decls =
             FStar_List.iter
               (fun x ->
                  collect_decl x.FStar_Parser_AST.d;
                  FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                  (match x.FStar_Parser_AST.d with
                   | FStar_Parser_AST.Val uu____2890 when
                       FStar_List.contains
                         FStar_Parser_AST.Inline_for_extraction
                         x.FStar_Parser_AST.quals
                       -> add_to_parsing_data P_inline_for_extraction
                   | uu____2895 -> ())) decls
           and collect_decl d =
             match d with
             | FStar_Parser_AST.Include lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Open lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Friend lid ->
                 let uu____2900 =
                   let uu____2901 =
                     let uu____2906 =
                       let uu____2907 = lowercase_join_longident lid true in
                       FStar_All.pipe_right uu____2907 FStar_Ident.lid_of_str in
                     (true, uu____2906) in
                   P_dep uu____2901 in
                 add_to_parsing_data uu____2900
             | FStar_Parser_AST.ModuleAbbrev (ident, lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStar_Parser_AST.TopLevelLet (uu____2910, patterms) ->
                 FStar_List.iter
                   (fun uu____2932 ->
                      match uu____2932 with
                      | (pat, t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStar_Parser_AST.Splice (uu____2940, t) -> collect_term t
             | FStar_Parser_AST.Assume (uu____2946, t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____2948;
                   FStar_Parser_AST.mdest = uu____2949;
                   FStar_Parser_AST.lift_op =
                     FStar_Parser_AST.NonReifiableLift t;_}
                 -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____2951;
                   FStar_Parser_AST.mdest = uu____2952;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                 -> collect_term t
             | FStar_Parser_AST.Val (uu____2954, t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____2956;
                   FStar_Parser_AST.mdest = uu____2957;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                     (t0, t1);_}
                 -> (collect_term t0; collect_term t1)
             | FStar_Parser_AST.Tycon (uu____2961, tc, ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStar_Parser_Const.mk_class_lid)
                  else ();
                  FStar_List.iter collect_tycon ts)
             | FStar_Parser_AST.Exception (uu____2970, t) ->
                 FStar_Util.iter_opt t collect_term
             | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.LayeredEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.Polymonadic_bind
                 (uu____2978, uu____2979, uu____2980, t) -> collect_term t
             | FStar_Parser_AST.Polymonadic_subcomp
                 (uu____2982, uu____2983, t) -> collect_term t
             | FStar_Parser_AST.Pragma uu____2985 -> ()
             | FStar_Parser_AST.TopLevelModule lid ->
                 (FStar_Util.incr num_of_toplevelmods;
                  (let uu____2988 =
                     let uu____2989 = FStar_ST.op_Bang num_of_toplevelmods in
                     uu____2989 > Prims.int_one in
                   if uu____2988
                   then
                     let uu____2996 =
                       let uu____3001 =
                         let uu____3002 = string_of_lid lid true in
                         FStar_Util.format1
                           "Automatic dependency analysis demands one module per file (module %s not supported)"
                           uu____3002 in
                       (FStar_Errors.Fatal_OneModulePerFile, uu____3001) in
                     let uu____3003 = FStar_Ident.range_of_lid lid in
                     FStar_Errors.raise_error uu____2996 uu____3003
                   else ()))
           and collect_tycon uu___6_3005 =
             match uu___6_3005 with
             | FStar_Parser_AST.TyconAbstract (uu____3006, binders, k) ->
                 (collect_binders binders; FStar_Util.iter_opt k collect_term)
             | FStar_Parser_AST.TyconAbbrev (uu____3018, binders, k, t) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  collect_term t)
             | FStar_Parser_AST.TyconRecord
                 (uu____3032, binders, k, identterms) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____3065 ->
                       match uu____3065 with
                       | (uu____3070, t) -> collect_term t) identterms)
             | FStar_Parser_AST.TyconVariant
                 (uu____3072, binders, k, identterms) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____3118 ->
                       match uu____3118 with
                       | (uu____3127, t, uu____3129) ->
                           FStar_Util.iter_opt t collect_term) identterms)
           and collect_effect_decl uu___7_3134 =
             match uu___7_3134 with
             | FStar_Parser_AST.DefineEffect (uu____3135, binders, t, decls)
                 ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStar_Parser_AST.RedefineEffect (uu____3149, binders, t) ->
                 (collect_binders binders; collect_term t)
           and collect_binders binders =
             FStar_List.iter collect_binder binders
           and collect_binder b =
             collect_aqual b.FStar_Parser_AST.aqual;
             (match b with
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                    (uu____3162, t);
                  FStar_Parser_AST.brange = uu____3164;
                  FStar_Parser_AST.blevel = uu____3165;
                  FStar_Parser_AST.aqual = uu____3166;_} -> collect_term t
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                    (uu____3169, t);
                  FStar_Parser_AST.brange = uu____3171;
                  FStar_Parser_AST.blevel = uu____3172;
                  FStar_Parser_AST.aqual = uu____3173;_} -> collect_term t
              | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu____3177;
                  FStar_Parser_AST.blevel = uu____3178;
                  FStar_Parser_AST.aqual = uu____3179;_} -> collect_term t
              | uu____3182 -> ())
           and collect_aqual uu___8_3183 =
             match uu___8_3183 with
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta
                 (FStar_Parser_AST.Arg_qualifier_meta_tac t)) ->
                 collect_term t
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta
                 (FStar_Parser_AST.Arg_qualifier_meta_attr t)) ->
                 collect_term t
             | uu____3188 -> ()
           and collect_term t = collect_term' t.FStar_Parser_AST.tm
           and collect_constant uu___9_3192 =
             match uu___9_3192 with
             | FStar_Const.Const_int
                 (uu____3193, FStar_Pervasives_Native.Some
                  (signedness, width))
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
                 let uu____3208 =
                   let uu____3209 =
                     let uu____3214 =
                       let uu____3215 =
                         FStar_Util.format2 "fstar.%sint%s" u w in
                       FStar_All.pipe_right uu____3215 FStar_Ident.lid_of_str in
                     (false, uu____3214) in
                   P_dep uu____3209 in
                 add_to_parsing_data uu____3208
             | FStar_Const.Const_char uu____3216 ->
                 let uu____3217 =
                   let uu____3218 =
                     let uu____3223 =
                       FStar_All.pipe_right "fstar.char"
                         FStar_Ident.lid_of_str in
                     (false, uu____3223) in
                   P_dep uu____3218 in
                 add_to_parsing_data uu____3217
             | FStar_Const.Const_float uu____3224 ->
                 let uu____3225 =
                   let uu____3226 =
                     let uu____3231 =
                       FStar_All.pipe_right "fstar.float"
                         FStar_Ident.lid_of_str in
                     (false, uu____3231) in
                   P_dep uu____3226 in
                 add_to_parsing_data uu____3225
             | uu____3232 -> ()
           and collect_term' uu___12_3233 =
             match uu___12_3233 with
             | FStar_Parser_AST.Wild -> ()
             | FStar_Parser_AST.Const c -> collect_constant c
             | FStar_Parser_AST.Op (s, ts) ->
                 ((let uu____3242 =
                     let uu____3243 = FStar_Ident.string_of_id s in
                     uu____3243 = "@" in
                   if uu____3242
                   then
                     let uu____3244 =
                       let uu____3245 =
                         let uu____3246 =
                           FStar_Ident.path_of_text
                             "FStar.List.Tot.Base.append" in
                         FStar_Ident.lid_of_path uu____3246
                           FStar_Range.dummyRange in
                       FStar_Parser_AST.Name uu____3245 in
                     collect_term' uu____3244
                   else ());
                  FStar_List.iter collect_term ts)
             | FStar_Parser_AST.Tvar uu____3248 -> ()
             | FStar_Parser_AST.Uvar uu____3249 -> ()
             | FStar_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Projector (lid, uu____3252) ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Construct (lid, termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStar_List.iter
                    (fun uu____3277 ->
                       match uu____3277 with
                       | (t, uu____3283) -> collect_term t) termimps)
             | FStar_Parser_AST.Abs (pats, t) ->
                 (collect_patterns pats; collect_term t)
             | FStar_Parser_AST.App (t1, t2, uu____3293) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Let (uu____3295, patterms, t) ->
                 (FStar_List.iter
                    (fun uu____3345 ->
                       match uu____3345 with
                       | (attrs_opt, (pat, t1)) ->
                           ((let uu____3374 =
                               FStar_Util.map_opt attrs_opt
                                 (FStar_List.iter collect_term) in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStar_Parser_AST.LetOpen (lid, t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStar_Parser_AST.Bind (uu____3383, t1, t2) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Seq (t1, t2) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.If (t1, t2, t3) ->
                 (collect_term t1; collect_term t2; collect_term t3)
             | FStar_Parser_AST.Match (t, bs) ->
                 (collect_term t; collect_branches bs)
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
                    (fun uu____3479 ->
                       match uu____3479 with
                       | (uu____3484, t1) -> collect_term t1) idterms)
             | FStar_Parser_AST.Project (t, uu____3487) -> collect_term t
             | FStar_Parser_AST.Product (binders, t) ->
                 (collect_binders binders; collect_term t)
             | FStar_Parser_AST.Sum (binders, t) ->
                 (FStar_List.iter
                    (fun uu___10_3516 ->
                       match uu___10_3516 with
                       | FStar_Util.Inl b -> collect_binder b
                       | FStar_Util.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStar_Parser_AST.QForall (binders, (uu____3524, ts), t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.QExists (binders, (uu____3558, ts), t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.Refine (binder, t) ->
                 (collect_binder binder; collect_term t)
             | FStar_Parser_AST.NamedTyp (uu____3594, t) -> collect_term t
             | FStar_Parser_AST.Paren t -> collect_term t
             | FStar_Parser_AST.Requires (t, uu____3598) -> collect_term t
             | FStar_Parser_AST.Ensures (t, uu____3604) -> collect_term t
             | FStar_Parser_AST.Labeled (t, uu____3610, uu____3611) ->
                 collect_term t
             | FStar_Parser_AST.Quote (t, uu____3613) -> collect_term t
             | FStar_Parser_AST.Antiquote t -> collect_term t
             | FStar_Parser_AST.VQuote t -> collect_term t
             | FStar_Parser_AST.Attributes cattributes ->
                 FStar_List.iter collect_term cattributes
             | FStar_Parser_AST.CalcProof (rel, init, steps) ->
                 ((let uu____3627 =
                     let uu____3628 =
                       let uu____3633 = FStar_Ident.lid_of_str "FStar.Calc" in
                       (false, uu____3633) in
                     P_dep uu____3628 in
                   add_to_parsing_data uu____3627);
                  collect_term rel;
                  collect_term init;
                  FStar_List.iter
                    (fun uu___11_3642 ->
                       match uu___11_3642 with
                       | FStar_Parser_AST.CalcStep (rel1, just, next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
           and collect_patterns ps = FStar_List.iter collect_pattern ps
           and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
           and collect_pattern' uu___13_3652 =
             match uu___13_3652 with
             | FStar_Parser_AST.PatVar (uu____3653, aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatTvar (uu____3659, aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
             | FStar_Parser_AST.PatOp uu____3668 -> ()
             | FStar_Parser_AST.PatConst uu____3669 -> ()
             | FStar_Parser_AST.PatApp (p, ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStar_Parser_AST.PatName uu____3677 -> ()
             | FStar_Parser_AST.PatList ps -> collect_patterns ps
             | FStar_Parser_AST.PatOr ps -> collect_patterns ps
             | FStar_Parser_AST.PatTuple (ps, uu____3685) ->
                 collect_patterns ps
             | FStar_Parser_AST.PatRecord lidpats ->
                 FStar_List.iter
                   (fun uu____3704 ->
                      match uu____3704 with
                      | (uu____3709, p) -> collect_pattern p) lidpats
             | FStar_Parser_AST.PatAscribed
                 (p, (t, FStar_Pervasives_Native.None)) ->
                 (collect_pattern p; collect_term t)
             | FStar_Parser_AST.PatAscribed
                 (p, (t, FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           and collect_branches bs = FStar_List.iter collect_branch bs
           and collect_branch uu____3754 =
             match uu____3754 with
             | (pat, t1, t2) ->
                 (collect_pattern pat;
                  FStar_Util.iter_opt t1 collect_term;
                  collect_term t2) in
           let uu____3772 = FStar_Parser_Driver.parse_file filename in
           match uu____3772 with
           | (ast, uu____3796) ->
               (collect_module ast;
                (let pd1 =
                   let uu____3811 =
                     let uu____3814 = FStar_ST.op_Bang pd in
                     FStar_List.rev uu____3814 in
                   Mk_pd uu____3811 in
                 let uu____3827 = from_parsing_data pd1 original_map filename in
                 match uu____3827 with
                 | (deps1, has_inline_for_extraction, mo_roots) ->
                     (pd1, deps1, has_inline_for_extraction, mo_roots))))
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____3879 = FStar_Util.smap_create Prims.int_zero in
  FStar_Util.mk_ref uu____3879
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache -> FStar_ST.op_Colon_Equals collect_one_cache cache
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph ->
    let uu____3978 = dep_graph in
    match uu____3978 with
    | Deps g -> let uu____3982 = FStar_Util.smap_copy g in Deps uu____3982
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
          let uu____4016 = dep_graph in
          match uu____4016 with
          | Deps dg ->
              let uu____4024 = deps_empty () in
              (match uu____4024 with
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
                             | uu____4060 -> d)) in
                   (FStar_Util.smap_fold dg
                      (fun filename ->
                         fun dep_node1 ->
                           fun uu____4068 ->
                             let uu____4069 =
                               let uu___992_4070 = dep_node1 in
                               let uu____4071 = widen_one dep_node1.edges in
                               { edges = uu____4071; color = White } in
                             FStar_Util.smap_add dg' filename uu____4069) ();
                    (let uu____4072 = FStar_ST.op_Bang widened1 in
                     (uu____4072, (Deps dg')))))
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____4198 filename =
              match uu____4198 with
              | (all_friends, all_files) ->
                  let dep_node1 =
                    let uu____4229 = deps_try_find dep_graph1 filename in
                    FStar_Util.must uu____4229 in
                  (match dep_node1.color with
                   | Gray ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black -> (all_friends, all_files)
                   | White ->
                       ((let uu____4253 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep") in
                         if uu____4253
                         then
                           let uu____4254 =
                             let uu____4255 =
                               FStar_List.map dep_to_string dep_node1.edges in
                             FStar_String.concat ", " uu____4255 in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____4254
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1014_4261 = dep_node1 in
                           { edges = (uu___1014_4261.edges); color = Gray });
                        (let uu____4262 =
                           let uu____4271 =
                             dependences_of file_system_map dep_graph1
                               root_files filename in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____4271 in
                         match uu____4262 with
                         | (all_friends1, all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1020_4298 = dep_node1 in
                                 {
                                   edges = (uu___1020_4298.edges);
                                   color = Black
                                 });
                              (let uu____4300 =
                                 FStar_Options.debug_at_level_no_module
                                   (FStar_Options.Other "Dep") in
                               if uu____4300
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____4302 =
                                 let uu____4305 =
                                   FStar_List.collect
                                     (fun uu___14_4310 ->
                                        match uu___14_4310 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node1.edges in
                                 FStar_List.append uu____4305 all_friends1 in
                               (uu____4302, (filename :: all_files1)))))))
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1 ->
                   fun k ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames in
            let uu____4355 = all_friend_deps dep_graph [] ([], []) root_files in
            match uu____4355 with
            | (friends, all_files_0) ->
                ((let uu____4385 =
                    FStar_Options.debug_at_level_no_module
                      (FStar_Options.Other "Dep") in
                  if uu____4385
                  then
                    let uu____4386 =
                      let uu____4387 =
                        FStar_Util.remove_dups (fun x -> fun y -> x = y)
                          friends in
                      FStar_String.concat ", " uu____4387 in
                    FStar_Util.print3
                      "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                      (FStar_String.concat ", " all_files_0) uu____4386
                      (FStar_String.concat ", " interfaces_needing_inlining)
                  else ());
                 (let uu____4395 =
                    widen_deps friends dep_graph file_system_map widened in
                  match uu____4395 with
                  | (widened1, dep_graph1) ->
                      let uu____4408 =
                        (let uu____4418 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep") in
                         if uu____4418
                         then
                           FStar_Util.print_string
                             "==============Phase2==================\n"
                         else ());
                        all_friend_deps dep_graph1 [] ([], []) root_files in
                      (match uu____4408 with
                       | (uu____4430, all_files) ->
                           ((let uu____4441 =
                               FStar_Options.debug_at_level_no_module
                                 (FStar_Options.Other "Dep") in
                             if uu____4441
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
          (let uu____4474 =
             FStar_Options.debug_at_level_no_module
               (FStar_Options.Other "Dep") in
           if uu____4474
           then
             FStar_Util.print_string
               "==============Phase1==================\n"
           else ());
          (let widened = false in
           let uu____4477 = (FStar_Options.cmi ()) && for_extraction in
           if uu____4477
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
            let uu____4528 =
              phase1 file_system_map dep_graph interfaces_needing_inlining
                for_extraction in
            match uu____4528 with
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
                let uu____4587 = FStar_Options.find_file fn in
                match uu____4587 with
                | FStar_Pervasives_Native.None ->
                    let uu____4590 =
                      let uu____4595 =
                        FStar_Util.format1 "File %s could not be found\n" fn in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____4595) in
                    FStar_Errors.raise_err uu____4590
                | FStar_Pervasives_Native.Some fn1 -> fn1)) in
      let dep_graph = deps_empty () in
      let file_system_map = build_map all_cmd_line_files1 in
      let interfaces_needing_inlining = FStar_Util.mk_ref [] in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l in
        let uu____4613 =
          let uu____4616 = FStar_ST.op_Bang interfaces_needing_inlining in l1
            :: uu____4616 in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____4613 in
      let parse_results = FStar_Util.smap_create (Prims.of_int (40)) in
      let rec discover_one file_name1 =
        let uu____4648 =
          let uu____4649 = deps_try_find dep_graph file_name1 in
          uu____4649 = FStar_Pervasives_Native.None in
        if uu____4648
        then
          let uu____4654 =
            let uu____4669 =
              let uu____4682 = FStar_ST.op_Bang collect_one_cache in
              FStar_Util.smap_try_find uu____4682 file_name1 in
            match uu____4669 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None ->
                let uu____4790 =
                  collect_one file_system_map file_name1
                    get_parsing_data_from_cache in
                (match uu____4790 with
                 | (parsing_data1, deps1, needs_interface_inlining,
                    additional_roots) ->
                     (parsing_data1,
                       (deps1, additional_roots, needs_interface_inlining))) in
          match uu____4654 with
          | (parsing_data1, (deps1, mo_roots, needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name1
               else ();
               FStar_Util.smap_add parse_results file_name1 parsing_data1;
               (let deps2 =
                  let module_name1 = lowercase_module_name file_name1 in
                  let uu____4872 =
                    (is_implementation file_name1) &&
                      (has_interface file_system_map module_name1) in
                  if uu____4872
                  then FStar_List.append deps1 [UseInterface module_name1]
                  else deps1 in
                let dep_node1 =
                  let uu____4877 = FStar_List.unique deps2 in
                  { edges = uu____4877; color = White } in
                deps_add_dep dep_graph file_name1 dep_node1;
                (let uu____4879 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps2 mo_roots) in
                 FStar_List.iter discover_one uu____4879)))
        else () in
      profile
        (fun uu____4885 -> FStar_List.iter discover_one all_cmd_line_files1)
        "FStar.Parser.Dep.discover";
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____4909 =
            let uu____4914 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename in
            (FStar_Errors.Fatal_CyclicDependence, uu____4914) in
          FStar_Errors.raise_err uu____4909) in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph in
         let mo_files = FStar_Util.mk_ref [] in
         let rec aux cycle filename =
           let node =
             let uu____4954 = deps_try_find dep_graph1 filename in
             match uu____4954 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None ->
                 let uu____4958 =
                   FStar_Util.format1
                     "Impossible: Failed to find dependencies of %s" filename in
                 failwith uu____4958 in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x ->
                     match x with
                     | UseInterface f ->
                         let uu____4969 =
                           implementation_of_internal file_system_map1 f in
                         (match uu____4969 with
                          | FStar_Pervasives_Native.None -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____4975 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____4979 =
                           implementation_of_internal file_system_map1 f in
                         (match uu____4979 with
                          | FStar_Pervasives_Native.None -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____4985 -> [x; UseImplementation f])
                     | uu____4988 -> [x])) in
           match node.color with
           | Gray -> cycle_detected dep_graph1 cycle filename
           | Black -> ()
           | White ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1141_4991 = node in
                   { edges = direct_deps; color = Gray });
                (let uu____4993 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename in
                 FStar_List.iter (fun k -> aux (k :: cycle) k) uu____4993);
                deps_add_dep dep_graph1 filename
                  (let uu___1146_5000 = node in
                   { edges = direct_deps; color = Black });
                (let uu____5001 = is_interface filename in
                 if uu____5001
                 then
                   let uu____5002 =
                     let uu____5005 = lowercase_module_name filename in
                     implementation_of_internal file_system_map1 uu____5005 in
                   FStar_Util.iter_opt uu____5002
                     (fun impl ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu____5009 =
                            let uu____5012 = FStar_ST.op_Bang mo_files in
                            impl :: uu____5012 in
                          FStar_ST.op_Colon_Equals mo_files uu____5009
                        else ())
                 else ())) in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu____5038 = FStar_ST.op_Bang mo_files in
          FStar_List.iter (aux []) uu____5038) in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f ->
               let m = lowercase_module_name f in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining in
        let uu____5072 =
          profile
            (fun uu____5087 ->
               let uu____5088 =
                 let uu____5089 = FStar_Options.codegen () in
                 uu____5089 <> FStar_Pervasives_Native.None in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____5088)
            "FStar.Parser.Dep.topological_dependences_of" in
        match uu____5072 with
        | (all_files, uu____5101) ->
            ((let uu____5107 =
                FStar_Options.debug_at_level_no_module
                  (FStar_Options.Other "Dep") in
              if uu____5107
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
    let uu____5142 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____5161 ->
              match uu____5161 with
              | (m, d) ->
                  let uu____5168 = FStar_Util.base64_encode d in
                  FStar_Util.format2 "%s:%s" m uu____5168)) in
    FStar_All.pipe_right uu____5142 (FStar_String.concat "\n")
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
              let uu____5192 = deps_try_find deps2 f in
              FStar_All.pipe_right uu____5192 FStar_Option.get in
            let files =
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                dep_node1.edges in
            let files1 =
              FStar_List.map (fun s -> FStar_Util.replace_chars s 32 "\\ ")
                files in
            FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))
let (print_raw : deps -> unit) =
  fun deps1 ->
    let uu____5210 = deps1.dep_graph in
    match uu____5210 with
    | Deps deps2 ->
        let uu____5214 =
          let uu____5215 =
            FStar_Util.smap_fold deps2
              (fun k ->
                 fun dep_node1 ->
                   fun out ->
                     let uu____5229 =
                       let uu____5230 =
                         let uu____5231 =
                           FStar_List.map dep_to_string dep_node1.edges in
                         FStar_All.pipe_right uu____5231
                           (FStar_String.concat ";\n\t") in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____5230 in
                     uu____5229 :: out) [] in
          FStar_All.pipe_right uu____5215 (FStar_String.concat ";;\n") in
        FStar_All.pipe_right uu____5214 FStar_Util.print_endline
let (print_full : deps -> unit) =
  fun deps1 ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref [] in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map in
      let visited_other_modules = FStar_Util.smap_create (Prims.of_int (41)) in
      let should_visit lc_module_name =
        (let uu____5276 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name in
         FStar_Option.isSome uu____5276) ||
          (let uu____5280 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name in
           FStar_Option.isNone uu____5280) in
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
            let uu____5307 =
              let uu____5310 = FStar_ST.op_Bang order in ml_file ::
                uu____5310 in
            FStar_ST.op_Colon_Equals order uu____5307 in
      let rec aux uu___15_5340 =
        match uu___15_5340 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some file_name1 ->
                  let uu____5358 = deps_try_find deps1.dep_graph file_name1 in
                  (match uu____5358 with
                   | FStar_Pervasives_Native.None ->
                       let uu____5361 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name1 in
                       failwith uu____5361
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____5363;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps in
                       aux immediate_deps1) in
            ((let uu____5370 = should_visit lc_module_name in
              if uu____5370
              then
                let ml_file_opt = mark_visiting lc_module_name in
                ((let uu____5375 = implementation_of deps1 lc_module_name in
                  visit_file uu____5375);
                 (let uu____5379 = interface_of deps1 lc_module_name in
                  visit_file uu____5379);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract) in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map in
      aux all_extracted_modules;
      (let uu____5387 = FStar_ST.op_Bang order in FStar_List.rev uu____5387) in
    let sb =
      let uu____5401 = FStar_BigInt.of_int_fs (Prims.of_int (10000)) in
      FStar_StringBuffer.create uu____5401 in
    let pr str =
      let uu____5408 = FStar_StringBuffer.add str sb in
      FStar_All.pipe_left (fun uu____5409 -> ()) uu____5408 in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n" in
    let keys = deps_keys deps1.dep_graph in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____5446 =
          let uu____5447 =
            let uu____5450 = FStar_Util.basename fst_file in
            check_and_strip_suffix uu____5450 in
          FStar_Option.get uu____5447 in
        FStar_Util.replace_chars uu____5446 46 "_" in
      let uu____5451 = FStar_String.op_Hat ml_base_name ext in
      FStar_Options.prepend_output_dir uu____5451 in
    let norm_path s =
      FStar_Util.replace_chars (FStar_Util.replace_chars s 92 "/") 32 "\\ " in
    let output_ml_file f =
      let uu____5464 = output_file ".ml" f in norm_path uu____5464 in
    let output_krml_file f =
      let uu____5471 = output_file ".krml" f in norm_path uu____5471 in
    let output_cmx_file f =
      let uu____5478 = output_file ".cmx" f in norm_path uu____5478 in
    let cache_file f =
      let uu____5485 = cache_file_name f in norm_path uu____5485 in
    let uu____5486 =
      phase1 deps1.file_system_map deps1.dep_graph
        deps1.interfaces_with_inlining true in
    match uu____5486 with
    | (widened, dep_graph) ->
        let all_checked_files =
          FStar_All.pipe_right keys
            (FStar_List.fold_left
               (fun all_checked_files ->
                  fun file_name1 ->
                    let process_one_key uu____5516 =
                      let dep_node1 =
                        let uu____5518 =
                          deps_try_find deps1.dep_graph file_name1 in
                        FStar_All.pipe_right uu____5518 FStar_Option.get in
                      let uu____5523 =
                        let uu____5534 = is_interface file_name1 in
                        if uu____5534
                        then
                          (FStar_Pervasives_Native.None,
                            FStar_Pervasives_Native.None)
                        else
                          (let uu____5554 =
                             let uu____5557 =
                               lowercase_module_name file_name1 in
                             interface_of deps1 uu____5557 in
                           match uu____5554 with
                           | FStar_Pervasives_Native.None ->
                               (FStar_Pervasives_Native.None,
                                 FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.Some iface ->
                               let uu____5577 =
                                 let uu____5582 =
                                   let uu____5585 =
                                     let uu____5586 =
                                       deps_try_find deps1.dep_graph iface in
                                     FStar_Option.get uu____5586 in
                                   uu____5585.edges in
                                 FStar_Pervasives_Native.Some uu____5582 in
                               ((FStar_Pervasives_Native.Some iface),
                                 uu____5577)) in
                      match uu____5523 with
                      | (iface_fn, iface_deps) ->
                          let iface_deps1 =
                            FStar_Util.map_opt iface_deps
                              (FStar_List.filter
                                 (fun iface_dep ->
                                    let uu____5625 =
                                      FStar_Util.for_some
                                        (dep_subsumed_by iface_dep)
                                        dep_node1.edges in
                                    Prims.op_Negation uu____5625)) in
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
                            let uu____5652 =
                              FStar_All.pipe_right iface_fn
                                FStar_Util.is_some in
                            if uu____5652
                            then
                              let iface_fn1 =
                                FStar_All.pipe_right iface_fn FStar_Util.must in
                              let uu____5660 =
                                FStar_All.pipe_right files1
                                  (FStar_List.filter
                                     (fun f -> f <> iface_fn1)) in
                              FStar_All.pipe_right uu____5660
                                (fun files2 ->
                                   let uu____5678 = cache_file_name iface_fn1 in
                                   uu____5678 :: files2)
                            else files1 in
                          let files3 = FStar_List.map norm_path files2 in
                          let files4 = FStar_String.concat "\\\n\t" files3 in
                          let cache_file_name1 = cache_file file_name1 in
                          let all_checked_files1 =
                            let uu____5688 =
                              let uu____5689 =
                                let uu____5690 =
                                  module_name_of_file file_name1 in
                                FStar_Options.should_be_already_cached
                                  uu____5690 in
                              Prims.op_Negation uu____5689 in
                            if uu____5688
                            then
                              (print_entry cache_file_name1 norm_f files4;
                               cache_file_name1
                               ::
                               all_checked_files)
                            else all_checked_files in
                          let uu____5695 =
                            let uu____5702 = FStar_Options.cmi () in
                            if uu____5702
                            then
                              profile
                                (fun uu____5717 ->
                                   let uu____5718 = dep_graph_copy dep_graph in
                                   topological_dependences_of'
                                     deps1.file_system_map uu____5718
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
                               let uu____5745 =
                                 FStar_Util.remove_dups
                                   (fun x -> fun y -> x = y)
                                   (FStar_List.append fst_files
                                      fst_files_from_iface) in
                               (uu____5745, false)) in
                          (match uu____5695 with
                           | (all_fst_files_dep, widened1) ->
                               let all_checked_fst_dep_files =
                                 FStar_All.pipe_right all_fst_files_dep
                                   (FStar_List.map cache_file) in
                               let all_checked_fst_dep_files_string =
                                 FStar_String.concat " \\\n\t"
                                   all_checked_fst_dep_files in
                               ((let uu____5771 =
                                   is_implementation file_name1 in
                                 if uu____5771
                                 then
                                   ((let uu____5773 =
                                       (FStar_Options.cmi ()) && widened1 in
                                     if uu____5773
                                     then
                                       ((let uu____5775 =
                                           output_ml_file file_name1 in
                                         print_entry uu____5775
                                           cache_file_name1
                                           all_checked_fst_dep_files_string);
                                        (let uu____5776 =
                                           output_krml_file file_name1 in
                                         print_entry uu____5776
                                           cache_file_name1
                                           all_checked_fst_dep_files_string))
                                     else
                                       ((let uu____5779 =
                                           output_ml_file file_name1 in
                                         print_entry uu____5779
                                           cache_file_name1 "");
                                        (let uu____5780 =
                                           output_krml_file file_name1 in
                                         print_entry uu____5780
                                           cache_file_name1 "")));
                                    (let cmx_files =
                                       let extracted_fst_files =
                                         FStar_All.pipe_right
                                           all_fst_files_dep
                                           (FStar_List.filter
                                              (fun df ->
                                                 (let uu____5797 =
                                                    lowercase_module_name df in
                                                  let uu____5798 =
                                                    lowercase_module_name
                                                      file_name1 in
                                                  uu____5797 <> uu____5798)
                                                   &&
                                                   (let uu____5800 =
                                                      lowercase_module_name
                                                        df in
                                                    FStar_Options.should_extract
                                                      uu____5800))) in
                                       FStar_All.pipe_right
                                         extracted_fst_files
                                         (FStar_List.map output_cmx_file) in
                                     let uu____5805 =
                                       let uu____5806 =
                                         lowercase_module_name file_name1 in
                                       FStar_Options.should_extract
                                         uu____5806 in
                                     if uu____5805
                                     then
                                       let cmx_files1 =
                                         FStar_String.concat "\\\n\t"
                                           cmx_files in
                                       let uu____5808 =
                                         output_cmx_file file_name1 in
                                       let uu____5809 =
                                         output_ml_file file_name1 in
                                       print_entry uu____5808 uu____5809
                                         cmx_files1
                                     else ()))
                                 else
                                   (let uu____5812 =
                                      (let uu____5815 =
                                         let uu____5816 =
                                           lowercase_module_name file_name1 in
                                         has_implementation
                                           deps1.file_system_map uu____5816 in
                                       Prims.op_Negation uu____5815) &&
                                        (is_interface file_name1) in
                                    if uu____5812
                                    then
                                      let uu____5817 =
                                        (FStar_Options.cmi ()) &&
                                          (widened1 || true) in
                                      (if uu____5817
                                       then
                                         let uu____5818 =
                                           output_krml_file file_name1 in
                                         print_entry uu____5818
                                           cache_file_name1
                                           all_checked_fst_dep_files_string
                                       else
                                         (let uu____5820 =
                                            output_krml_file file_name1 in
                                          print_entry uu____5820
                                            cache_file_name1 ""))
                                    else ()));
                                all_checked_files1)) in
                    profile process_one_key
                      "FStar.Parser.Dep.process_one_key") []) in
        let all_fst_files =
          let uu____5827 =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
          FStar_All.pipe_right uu____5827
            (FStar_Util.sort_with FStar_String.compare) in
        let all_fsti_files =
          let uu____5841 =
            FStar_All.pipe_right keys (FStar_List.filter is_interface) in
          FStar_All.pipe_right uu____5841
            (FStar_Util.sort_with FStar_String.compare) in
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.of_int (41)) in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file ->
                  let mname = lowercase_module_name fst_file in
                  let uu____5867 = FStar_Options.should_extract mname in
                  if uu____5867
                  then
                    let uu____5868 = output_ml_file fst_file in
                    FStar_Util.smap_add ml_file_map mname uu____5868
                  else ()));
          sort_output_files ml_file_map in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.of_int (41)) in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file ->
                  let mname = lowercase_module_name fst_file in
                  let uu____5884 = output_krml_file fst_file in
                  FStar_Util.smap_add krml_file_map mname uu____5884));
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
                   let uu____5925 = FStar_Range.def_range r in
                   FStar_Range.set_use_range r uu____5925 in
                 let uu____5926 =
                   let uu____5927 =
                     has_implementation deps1.file_system_map mn in
                   Prims.op_Negation uu____5927 in
                 if uu____5926
                 then
                   let uu____5928 = range_of_file fsti in
                   let uu____5929 =
                     let uu____5934 =
                       let uu____5935 = module_name_of_file fsti in
                       FStar_Util.format1
                         "Interface %s is admitted without an implementation"
                         uu____5935 in
                     (FStar_Errors.Warning_WarnOnUse, uu____5934) in
                   FStar_Errors.log_issue uu____5928 uu____5929
                 else ()));
         print_all "ALL_FST_FILES" all_fst_files;
         print_all "ALL_FSTI_FILES" all_fsti_files;
         print_all "ALL_CHECKED_FILES" all_checked_files;
         print_all "ALL_ML_FILES" all_ml_files;
         print_all "ALL_KRML_FILES" all_krml_files;
         FStar_StringBuffer.output_channel FStar_Util.stdout sb)
let (print : deps -> unit) =
  fun deps1 ->
    let uu____5947 = FStar_Options.dep () in
    match uu____5947 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps1
    | FStar_Pervasives_Native.Some "full" ->
        profile (fun uu____5951 -> print_full deps1)
          "FStar.Parser.Deps.print_full_deps"
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps1.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps1
    | FStar_Pervasives_Native.Some uu____5952 ->
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
         fun uu____5993 ->
           fun s ->
             match uu____5993 with
             | (v0, v1) ->
                 let uu____6013 =
                   let uu____6014 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1) in
                   FStar_String.op_Hat "; " uu____6014 in
                 FStar_String.op_Hat s uu____6013) ""
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps1 ->
    fun module_name1 ->
      let uu____6025 =
        let uu____6026 = FStar_Ident.string_of_lid module_name1 in
        FStar_String.lowercase uu____6026 in
      has_interface deps1.file_system_map uu____6025
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps1 ->
    fun module_name1 ->
      let m =
        let uu____6038 = FStar_Ident.string_of_lid module_name1 in
        FStar_String.lowercase uu____6038 in
      FStar_All.pipe_right deps1.all_files
        (FStar_Util.for_some
           (fun f ->
              (is_implementation f) &&
                (let uu____6044 =
                   let uu____6045 = module_name_of_file f in
                   FStar_String.lowercase uu____6045 in
                 uu____6044 = m)))