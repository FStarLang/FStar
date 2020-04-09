open Prims
let profile : 'uuuuuu16 . (unit -> 'uuuuuu16) -> Prims.string -> 'uuuuuu16 =
  fun f  ->
    fun c  -> FStar_Profiling.profile f FStar_Pervasives_Native.None c
  
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____44 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____55 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____66 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____89 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____100 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____111 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____122 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____133 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____181 =
             (l > lext) &&
               (let uu____184 = FStar_String.substring f (l - lext) lext  in
                uu____184 = ext)
              in
           if uu____181
           then
             let uu____191 =
               FStar_String.substring f Prims.int_zero (l - lext)  in
             FStar_Pervasives_Native.Some uu____191
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____198 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____198 with
    | (FStar_Pervasives_Native.Some m)::uu____212 ->
        FStar_Pervasives_Native.Some m
    | uu____224 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____241 =
      FStar_String.get f ((FStar_String.length f) - Prims.int_one)  in
    uu____241 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____255 = is_interface f  in Prims.op_Negation uu____255 
let list_of_option :
  'uuuuuu262 .
    'uuuuuu262 FStar_Pervasives_Native.option -> 'uuuuuu262 Prims.list
  =
  fun uu___0_271  ->
    match uu___0_271 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'uuuuuu280 .
    ('uuuuuu280 FStar_Pervasives_Native.option * 'uuuuuu280
      FStar_Pervasives_Native.option) -> 'uuuuuu280 Prims.list
  =
  fun uu____295  ->
    match uu____295 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____323 =
      let uu____327 = FStar_Util.basename f  in
      check_and_strip_suffix uu____327  in
    match uu____323 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____334 =
          let uu____340 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____340)  in
        FStar_Errors.raise_err uu____334
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____354 = module_name_of_file f  in
    FStar_String.lowercase uu____354
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____367 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____367 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____370 ->
        let uu____373 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____373
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____413 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____436 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____459 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____482 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_500  ->
    match uu___1_500 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'uuuuuu519 . unit -> 'uuuuuu519 Prims.list =
  fun uu____523  -> [] 
type dep_node = {
  edges: dependences ;
  color: color }
let (__proj__Mkdep_node__item__edges : dep_node -> dependences) =
  fun projectee  ->
    match projectee with | { edges; color = color1;_} -> edges
  
let (__proj__Mkdep_node__item__color : dep_node -> color) =
  fun projectee  ->
    match projectee with | { edges; color = color1;_} -> color1
  
type dependence_graph =
  | Deps of dep_node FStar_Util.smap 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee  -> true 
let (__proj__Deps__item___0 : dependence_graph -> dep_node FStar_Util.smap) =
  fun projectee  -> match projectee with | Deps _0 -> _0 
type parsing_data_elt =
  | P_begin_module of FStar_Ident.lident 
  | P_open of (Prims.bool * FStar_Ident.lident) 
  | P_open_module_or_namespace of (open_kind * FStar_Ident.lid) 
  | P_dep of (Prims.bool * FStar_Ident.lident) 
  | P_alias of (FStar_Ident.ident * FStar_Ident.lident) 
  | P_lid of FStar_Ident.lident 
  | P_inline_for_extraction 
let (uu___is_P_begin_module : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_begin_module _0 -> true | uu____636 -> false
  
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_begin_module _0 -> _0 
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_open _0 -> true | uu____660 -> false
  
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_open _0 -> _0 
let (uu___is_P_open_module_or_namespace : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_open_module_or_namespace _0 -> true
    | uu____698 -> false
  
let (__proj__P_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStar_Ident.lid)) =
  fun projectee  ->
    match projectee with | P_open_module_or_namespace _0 -> _0
  
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_dep _0 -> true | uu____734 -> false
  
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_dep _0 -> _0 
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_alias _0 -> true | uu____772 -> false
  
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_alias _0 -> _0 
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_lid _0 -> true | uu____803 -> false
  
let (__proj__P_lid__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_lid _0 -> _0 
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_inline_for_extraction  -> true
    | uu____821 -> false
  
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee  -> match projectee with | Mk_pd _0 -> _0 
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt  ->
    let str_of_open_kind uu___2_864 =
      match uu___2_864 with
      | Open_module  -> "P_open_module"
      | Open_namespace  -> "P_open_namespace"  in
    match elt with
    | P_begin_module lid ->
        let uu____870 =
          let uu____872 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____872 ")"  in
        FStar_String.op_Hat "P_begin_module (" uu____870
    | P_open (b,lid) ->
        let uu____880 =
          let uu____882 = FStar_Util.string_of_bool b  in
          let uu____884 =
            let uu____886 =
              let uu____888 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____888 ")"  in
            FStar_String.op_Hat ", " uu____886  in
          FStar_String.op_Hat uu____882 uu____884  in
        FStar_String.op_Hat "P_open (" uu____880
    | P_open_module_or_namespace (k,lid) ->
        let uu____895 =
          let uu____897 =
            let uu____899 =
              let uu____901 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____901 ")"  in
            FStar_String.op_Hat ", " uu____899  in
          FStar_String.op_Hat (str_of_open_kind k) uu____897  in
        FStar_String.op_Hat "P_open_module_or_namespace (" uu____895
    | P_dep (b,lid) ->
        let uu____910 =
          let uu____912 = FStar_Ident.text_of_lid lid  in
          let uu____914 =
            let uu____916 =
              let uu____918 = FStar_Util.string_of_bool b  in
              FStar_String.op_Hat uu____918 ")"  in
            FStar_String.op_Hat ", " uu____916  in
          FStar_String.op_Hat uu____912 uu____914  in
        FStar_String.op_Hat "P_dep (" uu____910
    | P_alias (id,lid) ->
        let uu____925 =
          let uu____927 = FStar_Ident.text_of_id id  in
          let uu____929 =
            let uu____931 =
              let uu____933 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____933 ")"  in
            FStar_String.op_Hat ", " uu____931  in
          FStar_String.op_Hat uu____927 uu____929  in
        FStar_String.op_Hat "P_alias (" uu____925
    | P_lid lid ->
        let uu____939 =
          let uu____941 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____941 ")"  in
        FStar_String.op_Hat "P_lid (" uu____939
    | P_inline_for_extraction  -> "P_inline_for_extraction"
  
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___3_952  ->
    match uu___3_952 with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s  ->
                fun elt  ->
                  let uu____967 =
                    let uu____969 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt  in
                    FStar_String.op_Hat "; " uu____969  in
                  FStar_String.op_Hat s uu____967) "")
  
let (parsing_data_elt_eq :
  parsing_data_elt -> parsing_data_elt -> Prims.bool) =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (P_begin_module l1,P_begin_module l2) -> FStar_Ident.lid_equals l1 l2
      | (P_open (b1,l1),P_open (b2,l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_open_module_or_namespace (k1,l1),P_open_module_or_namespace
         (k2,l2)) -> (k1 = k2) && (FStar_Ident.lid_equals l1 l2)
      | (P_dep (b1,l1),P_dep (b2,l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_alias (i1,l1),P_alias (i2,l2)) ->
          (let uu____1019 = FStar_Ident.text_of_id i1  in
           let uu____1021 = FStar_Ident.text_of_id i2  in
           uu____1019 = uu____1021) && (FStar_Ident.lid_equals l1 l2)
      | (P_lid l1,P_lid l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction ,P_inline_for_extraction ) -> true
      | (uu____1027,uu____1028) -> false
  
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
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> dep_graph
  
let (__proj__Mkdeps__item__file_system_map : deps -> files_for_module_name) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> file_system_map
  
let (__proj__Mkdeps__item__cmd_line_files : deps -> file_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> cmd_line_files
  
let (__proj__Mkdeps__item__all_files : deps -> file_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> all_files
  
let (__proj__Mkdeps__item__interfaces_with_inlining :
  deps -> module_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} ->
        interfaces_with_inlining
  
let (__proj__Mkdeps__item__parse_results :
  deps -> parsing_data FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> parse_results
  
let (deps_try_find :
  dependence_graph -> Prims.string -> dep_node FStar_Pervasives_Native.option)
  =
  fun uu____1244  ->
    fun k  -> match uu____1244 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____1266  ->
    fun k  ->
      fun v  -> match uu____1266 with | Deps m -> FStar_Util.smap_add m k v
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____1281  -> match uu____1281 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____1293  ->
    let uu____1294 = FStar_Util.smap_create (Prims.of_int (41))  in
    Deps uu____1294
  
let (mk_deps :
  dependence_graph ->
    files_for_module_name ->
      file_name Prims.list ->
        file_name Prims.list ->
          module_name Prims.list -> parsing_data FStar_Util.smap -> deps)
  =
  fun dg  ->
    fun fs  ->
      fun c  ->
        fun a  ->
          fun i  ->
            fun pr  ->
              {
                dep_graph = dg;
                file_system_map = fs;
                cmd_line_files = c;
                all_files = a;
                interfaces_with_inlining = i;
                parse_results = pr
              }
  
let (empty_deps : deps) =
  let uu____1352 = deps_empty ()  in
  let uu____1353 = FStar_Util.smap_create Prims.int_zero  in
  let uu____1365 = FStar_Util.smap_create Prims.int_zero  in
  mk_deps uu____1352 uu____1353 [] [] [] uu____1365 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___4_1378  ->
    match uu___4_1378 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
    | FriendImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1407 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1407 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1434) ->
          let uu____1456 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1456
      | FStar_Pervasives_Native.Some
          (uu____1459,FStar_Pervasives_Native.Some fn) ->
          let uu____1482 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1482
      | uu____1485 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1518 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1518 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1545) ->
          FStar_Pervasives_Native.Some iface
      | uu____1568 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1601 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1601 with
      | FStar_Pervasives_Native.Some
          (uu____1627,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1651 -> FStar_Pervasives_Native.None
  
let (interface_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps1  -> fun key  -> interface_of_internal deps1.file_system_map key 
let (implementation_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps1  ->
    fun key  -> implementation_of_internal deps1.file_system_map key
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1712 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1712
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1732 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1732
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax = FStar_Options.lax ()  in
    let cache_fn =
      if lax
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1767 =
      let uu____1771 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1771  in
    match uu____1767 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1782 =
            ((let uu____1786 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1786) &&
               (let uu____1792 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1792))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1795 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1795))
             in
          if uu____1782
          then
            let uu____1798 =
              let uu____1804 =
                let uu____1806 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expect %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1806
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1804)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1798
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1813 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1813
        then
          let uu____1819 =
            let uu____1825 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1825)
             in
          FStar_Errors.raise_err uu____1819
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.of_int (100))  in
  let memo1 f x =
    let uu____1861 = FStar_Util.smap_try_find memo x  in
    match uu____1861 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps1  ->
    fun fn  ->
      let uu____1888 = FStar_Util.smap_try_find deps1.parse_results fn  in
      FStar_All.pipe_right uu____1888 FStar_Util.must
  
let (file_of_dep_aux :
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name)
  =
  fun use_checked_file  ->
    fun file_system_map  ->
      fun all_cmd_line_files  ->
        fun d  ->
          let cmd_line_has_impl key =
            FStar_All.pipe_right all_cmd_line_files
              (FStar_Util.for_some
                 (fun fn  ->
                    (is_implementation fn) &&
                      (let uu____1942 = lowercase_module_name fn  in
                       key = uu____1942)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1961 = interface_of_internal file_system_map key  in
              (match uu____1961 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1968 =
                     let uu____1974 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1974)  in
                   FStar_Errors.raise_err uu____1968
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1984 =
                (cmd_line_has_impl key) &&
                  (let uu____1987 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1987)
                 in
              if uu____1984
              then
                let uu____1994 = FStar_Options.expose_interfaces ()  in
                (if uu____1994
                 then
                   let uu____1998 =
                     let uu____2000 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____2000  in
                   maybe_use_cache_of uu____1998
                 else
                   (let uu____2007 =
                      let uu____2013 =
                        let uu____2015 =
                          let uu____2017 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____2017  in
                        let uu____2022 =
                          let uu____2024 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____2024  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____2015 uu____2022
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____2013)
                       in
                    FStar_Errors.raise_err uu____2007))
              else
                (let uu____2034 =
                   let uu____2036 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____2036  in
                 maybe_use_cache_of uu____2034)
          | PreferInterface key ->
              let uu____2043 = implementation_of_internal file_system_map key
                 in
              (match uu____2043 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2049 =
                     let uu____2055 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2055)
                      in
                   FStar_Errors.raise_err uu____2049
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____2065 = implementation_of_internal file_system_map key
                 in
              (match uu____2065 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2071 =
                     let uu____2077 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2077)
                      in
                   FStar_Errors.raise_err uu____2071
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____2087 = implementation_of_internal file_system_map key
                 in
              (match uu____2087 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2093 =
                     let uu____2099 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2099)
                      in
                   FStar_Errors.raise_err uu____2093
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
  
let (file_of_dep :
  files_for_module_name -> file_name Prims.list -> dependence -> file_name) =
  file_of_dep_aux false 
let (dependences_of :
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list)
  =
  fun file_system_map  ->
    fun deps1  ->
      fun all_cmd_line_files  ->
        fun fn  ->
          let uu____2160 = deps_try_find deps1 fn  in
          match uu____2160 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps2; color = uu____2168;_} ->
              let uu____2169 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files) deps2
                 in
              FStar_All.pipe_right uu____2169
                (FStar_List.filter (fun k  -> k <> fn))
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____2197 =
       let uu____2199 =
         let uu____2201 =
           let uu____2203 =
             let uu____2207 =
               let uu____2211 = deps_keys graph  in
               FStar_List.unique uu____2211  in
             FStar_List.collect
               (fun k  ->
                  let deps1 =
                    let uu____2225 =
                      let uu____2226 = deps_try_find graph k  in
                      FStar_Util.must uu____2226  in
                    uu____2225.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print dep =
                    let uu____2247 =
                      let uu____2249 = lowercase_module_name k  in
                      r uu____2249  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2247
                      (r (module_name_of_dep dep))
                     in
                  FStar_List.map print deps1) uu____2207
              in
           FStar_String.concat "\n" uu____2203  in
         FStar_String.op_Hat uu____2201 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____2199  in
     FStar_Util.write_file "dep.graph" uu____2197)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____2270  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____2296 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____2296  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____2336 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____2336
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____2373 =
              let uu____2379 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____2379)  in
            FStar_Errors.raise_err uu____2373)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map = FStar_Util.smap_create (Prims.of_int (41))  in
    let add_entry key full_path =
      let uu____2442 = FStar_Util.smap_try_find map key  in
      match uu____2442 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2489 = is_interface full_path  in
          if uu____2489
          then
            FStar_Util.smap_add map key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2538 = is_interface full_path  in
          if uu____2538
          then
            FStar_Util.smap_add map key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2580 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2598  ->
          match uu____2598 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2580);
    FStar_List.iter
      (fun f  ->
         let uu____2617 = lowercase_module_name f  in add_entry uu____2617 f)
      filenames;
    map
  
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool)
  =
  fun original_map  ->
    fun working_map  ->
      fun prefix  ->
        let found = FStar_Util.mk_ref false  in
        let prefix1 = FStar_String.op_Hat prefix "."  in
        FStar_Util.smap_iter original_map
          (fun k  ->
             fun uu____2665  ->
               if FStar_Util.starts_with k prefix1
               then
                 let suffix =
                   FStar_String.substring k (FStar_String.length prefix1)
                     ((FStar_String.length k) - (FStar_String.length prefix1))
                    in
                 let filename =
                   let uu____2691 = FStar_Util.smap_try_find original_map k
                      in
                   FStar_Util.must uu____2691  in
                 (FStar_Util.smap_add working_map suffix filename;
                  FStar_ST.op_Colon_Equals found true)
               else ());
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last  ->
      let suffix =
        if last then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2811 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2811 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last  ->
      let uu____2834 = string_of_lid l last  in
      FStar_String.lowercase uu____2834
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2843 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2843
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2865 =
        let uu____2867 =
          let uu____2869 =
            let uu____2871 =
              let uu____2875 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2875  in
            FStar_Util.must uu____2871  in
          FStar_String.lowercase uu____2869  in
        uu____2867 <> k'  in
      if uu____2865
      then
        let uu____2880 = FStar_Ident.range_of_lid lid  in
        let uu____2881 =
          let uu____2887 =
            let uu____2889 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2889 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2887)  in
        FStar_Errors.log_issue uu____2880 uu____2881
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2905 -> false
  
let (core_modules : Prims.string Prims.list) =
  let uu____2911 =
    let uu____2915 = FStar_Options.prims_basename ()  in
    let uu____2917 =
      let uu____2921 = FStar_Options.pervasives_basename ()  in
      let uu____2923 =
        let uu____2927 = FStar_Options.pervasives_native_basename ()  in
        [uu____2927]  in
      uu____2921 :: uu____2923  in
    uu____2915 :: uu____2917  in
  FStar_All.pipe_right uu____2911 (FStar_List.map module_name_of_file) 
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let uu____2957 =
      let uu____2959 = module_name_of_file filename  in
      FStar_List.mem uu____2959 core_modules  in
    if uu____2957
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2998 =
         let uu____3001 = lowercase_module_name full_filename  in
         namespace_of_module uu____3001  in
       match uu____2998 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____3040 -> d = d'
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        (parsing_data * dependence Prims.list * Prims.bool * dependence
          Prims.list))
  =
  fun original_map  ->
    fun filename  ->
      fun get_parsing_data_from_cache  ->
        let from_parsing_data pd original_map1 filename1 =
          let deps1 = FStar_Util.mk_ref []  in
          let has_inline_for_extraction = FStar_Util.mk_ref false  in
          let mo_roots =
            let mname = lowercase_module_name filename1  in
            let uu____3158 =
              (is_interface filename1) &&
                (has_implementation original_map1 mname)
               in
            if uu____3158 then [UseImplementation mname] else []  in
          let auto_open =
            let uu____3168 = hard_coded_dependencies filename1  in
            FStar_All.pipe_right uu____3168
              (FStar_List.map
                 (fun uu____3190  ->
                    match uu____3190 with
                    | (lid,k) -> P_open_module_or_namespace (k, lid)))
             in
          let working_map = FStar_Util.smap_copy original_map1  in
          let set_interface_inlining uu____3225 =
            let uu____3226 = is_interface filename1  in
            if uu____3226
            then FStar_ST.op_Colon_Equals has_inline_for_extraction true
            else ()  in
          let add_dep deps2 d =
            let uu____3348 =
              let uu____3350 =
                let uu____3352 = FStar_ST.op_Bang deps2  in
                FStar_List.existsML (dep_subsumed_by d) uu____3352  in
              Prims.op_Negation uu____3350  in
            if uu____3348
            then
              let uu____3379 =
                let uu____3382 = FStar_ST.op_Bang deps2  in d :: uu____3382
                 in
              FStar_ST.op_Colon_Equals deps2 uu____3379
            else ()  in
          let dep_edge module_name1 is_friend =
            if is_friend
            then FriendImplementation module_name1
            else PreferInterface module_name1  in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true  in
            let uu____3473 = resolve_module_name original_or_working_map key
               in
            match uu____3473 with
            | FStar_Pervasives_Native.Some module_name1 ->
                (add_dep deps1 (dep_edge module_name1 is_friend); true)
            | uu____3483 -> false  in
          let record_open_module let_open lid =
            let uu____3502 =
              (let_open && (add_dependence_edge working_map lid false)) ||
                ((Prims.op_Negation let_open) &&
                   (add_dependence_edge original_map1 lid false))
               in
            if uu____3502
            then true
            else
              (if let_open
               then
                 (let uu____3513 = FStar_Ident.range_of_lid lid  in
                  let uu____3514 =
                    let uu____3520 =
                      let uu____3522 = string_of_lid lid true  in
                      FStar_Util.format1 "Module not found: %s" uu____3522
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3520)
                     in
                  FStar_Errors.log_issue uu____3513 uu____3514)
               else ();
               false)
             in
          let record_open_namespace lid =
            let key = lowercase_join_longident lid true  in
            let r = enter_namespace original_map1 working_map key  in
            if Prims.op_Negation r
            then
              let uu____3542 = FStar_Ident.range_of_lid lid  in
              let uu____3543 =
                let uu____3549 =
                  let uu____3551 = string_of_lid lid true  in
                  FStar_Util.format1
                    "No modules in namespace %s and no file with that name either"
                    uu____3551
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3549)
                 in
              FStar_Errors.log_issue uu____3542 uu____3543
            else ()  in
          let record_open let_open lid =
            let uu____3571 = record_open_module let_open lid  in
            if uu____3571
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid
              else ()
             in
          let record_open_module_or_namespace uu____3588 =
            match uu____3588 with
            | (lid,kind) ->
                (match kind with
                 | Open_namespace  -> record_open_namespace lid
                 | Open_module  ->
                     let uu____3595 = record_open_module false lid  in ())
             in
          let record_module_alias ident lid =
            let key =
              let uu____3612 = FStar_Ident.text_of_id ident  in
              FStar_String.lowercase uu____3612  in
            let alias = lowercase_join_longident lid true  in
            let uu____3617 = FStar_Util.smap_try_find original_map1 alias  in
            match uu____3617 with
            | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                (FStar_Util.smap_add working_map key deps_of_aliased_module;
                 (let uu____3674 =
                    let uu____3675 = lowercase_join_longident lid true  in
                    dep_edge uu____3675 false  in
                  add_dep deps1 uu____3674);
                 true)
            | FStar_Pervasives_Native.None  ->
                ((let uu____3691 = FStar_Ident.range_of_lid lid  in
                  let uu____3692 =
                    let uu____3698 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3698)
                     in
                  FStar_Errors.log_issue uu____3691 uu____3692);
                 false)
             in
          let add_dep_on_module module_name1 is_friend =
            let uu____3716 =
              add_dependence_edge working_map module_name1 is_friend  in
            if uu____3716
            then ()
            else
              (let uu____3721 =
                 FStar_Options.debug_at_level_no_module
                   (FStar_Options.Other "Dep")
                  in
               if uu____3721
               then
                 let uu____3725 = FStar_Ident.range_of_lid module_name1  in
                 let uu____3726 =
                   let uu____3732 =
                     let uu____3734 = FStar_Ident.string_of_lid module_name1
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____3734
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____3732)
                    in
                 FStar_Errors.log_issue uu____3725 uu____3726
               else ())
             in
          let record_lid lid =
            match lid.FStar_Ident.ns with
            | [] -> ()
            | uu____3746 ->
                let module_name1 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                   in
                add_dep_on_module module_name1 false
             in
          let begin_module lid =
            if (FStar_List.length lid.FStar_Ident.ns) > Prims.int_zero
            then
              let uu____3759 =
                let uu____3761 = namespace_of_lid lid  in
                enter_namespace original_map1 working_map uu____3761  in
              ()
            else ()  in
          (match pd with
           | Mk_pd l ->
               FStar_All.pipe_right (FStar_List.append auto_open l)
                 (FStar_List.iter
                    (fun elt  ->
                       match elt with
                       | P_begin_module lid -> begin_module lid
                       | P_open (b,lid) -> record_open b lid
                       | P_open_module_or_namespace (k,lid) ->
                           record_open_module_or_namespace (lid, k)
                       | P_dep (b,lid) -> add_dep_on_module lid b
                       | P_alias (id,lid) ->
                           let uu____3787 = record_module_alias id lid  in ()
                       | P_lid lid -> record_lid lid
                       | P_inline_for_extraction  ->
                           set_interface_inlining ())));
          (let uu____3790 = FStar_ST.op_Bang deps1  in
           let uu____3816 = FStar_ST.op_Bang has_inline_for_extraction  in
           (uu____3790, uu____3816, mo_roots))
           in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____3850 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____3850
        then
          ((let uu____3870 =
              FStar_Options.debug_at_level_no_module
                (FStar_Options.Other "Dep")
               in
            if uu____3870
            then
              FStar_Util.print1
                "Reading the parsing data for %s from its checked file\n"
                filename
            else ());
           (let uu____3877 =
              let uu____3889 =
                FStar_All.pipe_right data_from_cache FStar_Util.must  in
              from_parsing_data uu____3889 original_map filename  in
            match uu____3877 with
            | (deps1,has_inline_for_extraction,mo_roots) ->
                let uu____3918 =
                  FStar_All.pipe_right data_from_cache FStar_Util.must  in
                (uu____3918, deps1, has_inline_for_extraction, mo_roots)))
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref Prims.int_zero  in
           let pd = FStar_Util.mk_ref []  in
           let add_to_parsing_data elt =
             let uu____3947 =
               let uu____3949 =
                 let uu____3951 = FStar_ST.op_Bang pd  in
                 FStar_List.existsML (fun e  -> parsing_data_elt_eq e elt)
                   uu____3951
                  in
               Prims.op_Negation uu____3949  in
             if uu____3947
             then
               let uu____3980 =
                 let uu____3983 = FStar_ST.op_Bang pd  in elt :: uu____3983
                  in
               FStar_ST.op_Colon_Equals pd uu____3980
             else ()  in
           let rec collect_module uu___5_4140 =
             match uu___5_4140 with
             | FStar_Parser_AST.Module (lid,decls) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
             | FStar_Parser_AST.Interface (lid,decls,uu____4151) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
           
           and collect_decls decls =
             FStar_List.iter
               (fun x  ->
                  collect_decl x.FStar_Parser_AST.d;
                  FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                  (match x.FStar_Parser_AST.d with
                   | FStar_Parser_AST.Val uu____4170 when
                       FStar_List.contains
                         FStar_Parser_AST.Inline_for_extraction
                         x.FStar_Parser_AST.quals
                       -> add_to_parsing_data P_inline_for_extraction
                   | uu____4175 -> ())) decls
           
           and collect_decl d =
             match d with
             | FStar_Parser_AST.Include lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Open lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Friend lid ->
                 let uu____4184 =
                   let uu____4185 =
                     let uu____4191 =
                       let uu____4192 = lowercase_join_longident lid true  in
                       FStar_All.pipe_right uu____4192 FStar_Ident.lid_of_str
                        in
                     (true, uu____4191)  in
                   P_dep uu____4185  in
                 add_to_parsing_data uu____4184
             | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStar_Parser_AST.TopLevelLet (uu____4200,patterms) ->
                 FStar_List.iter
                   (fun uu____4222  ->
                      match uu____4222 with
                      | (pat,t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStar_Parser_AST.Main t -> collect_term t
             | FStar_Parser_AST.Splice (uu____4231,t) -> collect_term t
             | FStar_Parser_AST.Assume (uu____4237,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4239;
                   FStar_Parser_AST.mdest = uu____4240;
                   FStar_Parser_AST.lift_op =
                     FStar_Parser_AST.NonReifiableLift t;_}
                 -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4242;
                   FStar_Parser_AST.mdest = uu____4243;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                 -> collect_term t
             | FStar_Parser_AST.Val (uu____4245,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4247;
                   FStar_Parser_AST.mdest = uu____4248;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                     (t0,t1);_}
                 -> (collect_term t0; collect_term t1)
             | FStar_Parser_AST.Tycon (uu____4252,tc,ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStar_Parser_Const.mk_class_lid)
                  else ();
                  FStar_List.iter collect_tycon ts)
             | FStar_Parser_AST.Exception (uu____4267,t) ->
                 FStar_Util.iter_opt t collect_term
             | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.LayeredEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.Polymonadic_bind
                 (uu____4275,uu____4276,uu____4277,bind) -> collect_term bind
             | FStar_Parser_AST.Pragma uu____4279 -> ()
             | FStar_Parser_AST.TopLevelModule lid ->
                 (FStar_Util.incr num_of_toplevelmods;
                  (let uu____4282 =
                     let uu____4284 = FStar_ST.op_Bang num_of_toplevelmods
                        in
                     uu____4284 > Prims.int_one  in
                   if uu____4282
                   then
                     let uu____4309 =
                       let uu____4315 =
                         let uu____4317 = string_of_lid lid true  in
                         FStar_Util.format1
                           "Automatic dependency analysis demands one module per file (module %s not supported)"
                           uu____4317
                          in
                       (FStar_Errors.Fatal_OneModulePerFile, uu____4315)  in
                     let uu____4322 = FStar_Ident.range_of_lid lid  in
                     FStar_Errors.raise_error uu____4309 uu____4322
                   else ()))
           
           and collect_tycon uu___6_4325 =
             match uu___6_4325 with
             | FStar_Parser_AST.TyconAbstract (uu____4326,binders,k) ->
                 (collect_binders binders; FStar_Util.iter_opt k collect_term)
             | FStar_Parser_AST.TyconAbbrev (uu____4338,binders,k,t) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  collect_term t)
             | FStar_Parser_AST.TyconRecord (uu____4352,binders,k,identterms)
                 ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4385  ->
                       match uu____4385 with
                       | (uu____4390,t) -> collect_term t) identterms)
             | FStar_Parser_AST.TyconVariant
                 (uu____4392,binders,k,identterms) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4441  ->
                       match uu____4441 with
                       | (uu____4451,t,uu____4453) ->
                           FStar_Util.iter_opt t collect_term) identterms)
           
           and collect_effect_decl uu___7_4460 =
             match uu___7_4460 with
             | FStar_Parser_AST.DefineEffect (uu____4461,binders,t,decls) ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStar_Parser_AST.RedefineEffect (uu____4475,binders,t) ->
                 (collect_binders binders; collect_term t)
           
           and collect_binders binders =
             FStar_List.iter collect_binder binders
           
           and collect_binder b =
             collect_aqual b.FStar_Parser_AST.aqual;
             (match b with
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                    (uu____4488,t);
                  FStar_Parser_AST.brange = uu____4490;
                  FStar_Parser_AST.blevel = uu____4491;
                  FStar_Parser_AST.aqual = uu____4492;_} -> collect_term t
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                    (uu____4495,t);
                  FStar_Parser_AST.brange = uu____4497;
                  FStar_Parser_AST.blevel = uu____4498;
                  FStar_Parser_AST.aqual = uu____4499;_} -> collect_term t
              | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu____4503;
                  FStar_Parser_AST.blevel = uu____4504;
                  FStar_Parser_AST.aqual = uu____4505;_} -> collect_term t
              | uu____4508 -> ())
           
           and collect_aqual uu___8_4509 =
             match uu___8_4509 with
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                 collect_term t
             | uu____4513 -> ()
           
           and collect_term t = collect_term' t.FStar_Parser_AST.tm
           
           and collect_constant uu___9_4517 =
             match uu___9_4517 with
             | FStar_Const.Const_int
                 (uu____4518,FStar_Pervasives_Native.Some (signedness,width))
                 ->
                 let u =
                   match signedness with
                   | FStar_Const.Unsigned  -> "u"
                   | FStar_Const.Signed  -> ""  in
                 let w =
                   match width with
                   | FStar_Const.Int8  -> "8"
                   | FStar_Const.Int16  -> "16"
                   | FStar_Const.Int32  -> "32"
                   | FStar_Const.Int64  -> "64"  in
                 let uu____4545 =
                   let uu____4546 =
                     let uu____4552 =
                       let uu____4553 =
                         FStar_Util.format2 "fstar.%sint%s" u w  in
                       FStar_All.pipe_right uu____4553 FStar_Ident.lid_of_str
                        in
                     (false, uu____4552)  in
                   P_dep uu____4546  in
                 add_to_parsing_data uu____4545
             | FStar_Const.Const_char uu____4559 ->
                 let uu____4561 =
                   let uu____4562 =
                     let uu____4568 =
                       FStar_All.pipe_right "fstar.char"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4568)  in
                   P_dep uu____4562  in
                 add_to_parsing_data uu____4561
             | FStar_Const.Const_float uu____4573 ->
                 let uu____4574 =
                   let uu____4575 =
                     let uu____4581 =
                       FStar_All.pipe_right "fstar.float"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4581)  in
                   P_dep uu____4575  in
                 add_to_parsing_data uu____4574
             | uu____4586 -> ()
           
           and collect_term' uu___12_4587 =
             match uu___12_4587 with
             | FStar_Parser_AST.Wild  -> ()
             | FStar_Parser_AST.Const c -> collect_constant c
             | FStar_Parser_AST.Op (s,ts) ->
                 ((let uu____4596 =
                     let uu____4598 = FStar_Ident.text_of_id s  in
                     uu____4598 = "@"  in
                   if uu____4596
                   then
                     let uu____4603 =
                       let uu____4604 =
                         let uu____4605 =
                           FStar_Ident.path_of_text
                             "FStar.List.Tot.Base.append"
                            in
                         FStar_Ident.lid_of_path uu____4605
                           FStar_Range.dummyRange
                          in
                       FStar_Parser_AST.Name uu____4604  in
                     collect_term' uu____4603
                   else ());
                  FStar_List.iter collect_term ts)
             | FStar_Parser_AST.Tvar uu____4609 -> ()
             | FStar_Parser_AST.Uvar uu____4610 -> ()
             | FStar_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Projector (lid,uu____4613) ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Construct (lid,termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStar_List.iter
                    (fun uu____4638  ->
                       match uu____4638 with
                       | (t,uu____4644) -> collect_term t) termimps)
             | FStar_Parser_AST.Abs (pats,t) ->
                 (collect_patterns pats; collect_term t)
             | FStar_Parser_AST.App (t1,t2,uu____4654) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Let (uu____4656,patterms,t) ->
                 (FStar_List.iter
                    (fun uu____4706  ->
                       match uu____4706 with
                       | (attrs_opt,(pat,t1)) ->
                           ((let uu____4735 =
                               FStar_Util.map_opt attrs_opt
                                 (FStar_List.iter collect_term)
                                in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStar_Parser_AST.LetOpen (lid,t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStar_Parser_AST.Bind (uu____4746,t1,t2) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Seq (t1,t2) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.If (t1,t2,t3) ->
                 (collect_term t1; collect_term t2; collect_term t3)
             | FStar_Parser_AST.Match (t,bs) ->
                 (collect_term t; collect_branches bs)
             | FStar_Parser_AST.TryWith (t,bs) ->
                 (collect_term t; collect_branches bs)
             | FStar_Parser_AST.Ascribed
                 (t1,t2,FStar_Pervasives_Native.None ) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Ascribed
                 (t1,t2,FStar_Pervasives_Native.Some tac) ->
                 (collect_term t1; collect_term t2; collect_term tac)
             | FStar_Parser_AST.Record (t,idterms) ->
                 (FStar_Util.iter_opt t collect_term;
                  FStar_List.iter
                    (fun uu____4842  ->
                       match uu____4842 with
                       | (uu____4847,t1) -> collect_term t1) idterms)
             | FStar_Parser_AST.Project (t,uu____4850) -> collect_term t
             | FStar_Parser_AST.Product (binders,t) ->
                 (collect_binders binders; collect_term t)
             | FStar_Parser_AST.Sum (binders,t) ->
                 (FStar_List.iter
                    (fun uu___10_4879  ->
                       match uu___10_4879 with
                       | FStar_Util.Inl b -> collect_binder b
                       | FStar_Util.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStar_Parser_AST.QForall (binders,(uu____4887,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.QExists (binders,(uu____4921,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.Refine (binder,t) ->
                 (collect_binder binder; collect_term t)
             | FStar_Parser_AST.NamedTyp (uu____4957,t) -> collect_term t
             | FStar_Parser_AST.Paren t -> collect_term t
             | FStar_Parser_AST.Requires (t,uu____4961) -> collect_term t
             | FStar_Parser_AST.Ensures (t,uu____4969) -> collect_term t
             | FStar_Parser_AST.Labeled (t,uu____4977,uu____4978) ->
                 collect_term t
             | FStar_Parser_AST.Quote (t,uu____4984) -> collect_term t
             | FStar_Parser_AST.Antiquote t -> collect_term t
             | FStar_Parser_AST.VQuote t -> collect_term t
             | FStar_Parser_AST.Attributes cattributes ->
                 FStar_List.iter collect_term cattributes
             | FStar_Parser_AST.CalcProof (rel,init,steps) ->
                 ((let uu____4998 =
                     let uu____4999 =
                       let uu____5005 = FStar_Ident.lid_of_str "FStar.Calc"
                          in
                       (false, uu____5005)  in
                     P_dep uu____4999  in
                   add_to_parsing_data uu____4998);
                  collect_term rel;
                  collect_term init;
                  FStar_List.iter
                    (fun uu___11_5017  ->
                       match uu___11_5017 with
                       | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
           
           and collect_patterns ps = FStar_List.iter collect_pattern ps
           
           and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
           
           and collect_pattern' uu___13_5027 =
             match uu___13_5027 with
             | FStar_Parser_AST.PatVar (uu____5028,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatTvar (uu____5034,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
             | FStar_Parser_AST.PatOp uu____5043 -> ()
             | FStar_Parser_AST.PatConst uu____5044 -> ()
             | FStar_Parser_AST.PatApp (p,ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStar_Parser_AST.PatName uu____5052 -> ()
             | FStar_Parser_AST.PatList ps -> collect_patterns ps
             | FStar_Parser_AST.PatOr ps -> collect_patterns ps
             | FStar_Parser_AST.PatTuple (ps,uu____5060) ->
                 collect_patterns ps
             | FStar_Parser_AST.PatRecord lidpats ->
                 FStar_List.iter
                   (fun uu____5081  ->
                      match uu____5081 with
                      | (uu____5086,p) -> collect_pattern p) lidpats
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.None )) ->
                 (collect_pattern p; collect_term t)
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           
           and collect_branches bs = FStar_List.iter collect_branch bs
           
           and collect_branch uu____5131 =
             match uu____5131 with
             | (pat,t1,t2) ->
                 (collect_pattern pat;
                  FStar_Util.iter_opt t1 collect_term;
                  collect_term t2)
            in
           let uu____5149 = FStar_Parser_Driver.parse_file filename  in
           match uu____5149 with
           | (ast,uu____5175) ->
               (collect_module ast;
                (let pd1 =
                   let uu____5192 =
                     let uu____5195 = FStar_ST.op_Bang pd  in
                     FStar_List.rev uu____5195  in
                   Mk_pd uu____5192  in
                 let uu____5221 = from_parsing_data pd1 original_map filename
                    in
                 match uu____5221 with
                 | (deps1,has_inline_for_extraction,mo_roots) ->
                     (pd1, deps1, has_inline_for_extraction, mo_roots))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____5280 = FStar_Util.smap_create Prims.int_zero  in
  FStar_Util.mk_ref uu____5280 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5402 = dep_graph  in
    match uu____5402 with
    | Deps g -> let uu____5406 = FStar_Util.smap_copy g  in Deps uu____5406
  
let (widen_deps :
  module_name Prims.list ->
    dependence_graph ->
      files_for_module_name -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun friends  ->
    fun dep_graph  ->
      fun file_system_map  ->
        fun widened  ->
          let widened1 = FStar_Util.mk_ref widened  in
          let uu____5448 = dep_graph  in
          match uu____5448 with
          | Deps dg ->
              let uu____5457 = deps_empty ()  in
              (match uu____5457 with
               | Deps dg' ->
                   let widen_one deps1 =
                     FStar_All.pipe_right deps1
                       (FStar_List.map
                          (fun d  ->
                             match d with
                             | PreferInterface m when
                                 (FStar_List.contains m friends) &&
                                   (has_implementation file_system_map m)
                                 ->
                                 (FStar_ST.op_Colon_Equals widened1 true;
                                  FriendImplementation m)
                             | uu____5512 -> d))
                      in
                   (FStar_Util.smap_fold dg
                      (fun filename  ->
                         fun dep_node1  ->
                           fun uu____5520  ->
                             let uu____5522 =
                               let uu___984_5523 = dep_node1  in
                               let uu____5524 = widen_one dep_node1.edges  in
                               { edges = uu____5524; color = White }  in
                             FStar_Util.smap_add dg' filename uu____5522) ();
                    (let uu____5525 = FStar_ST.op_Bang widened1  in
                     (uu____5525, (Deps dg')))))
  
let (topological_dependences_of' :
  files_for_module_name ->
    dependence_graph ->
      Prims.string Prims.list ->
        file_name Prims.list ->
          Prims.bool -> (file_name Prims.list * Prims.bool))
  =
  fun file_system_map  ->
    fun dep_graph  ->
      fun interfaces_needing_inlining  ->
        fun root_files  ->
          fun widened  ->
            let rec all_friend_deps_1 dep_graph1 cycle uu____5691 filename =
              match uu____5691 with
              | (all_friends,all_files) ->
                  let dep_node1 =
                    let uu____5732 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5732  in
                  (match dep_node1.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5763 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep")
                            in
                         if uu____5763
                         then
                           let uu____5767 =
                             let uu____5769 =
                               FStar_List.map dep_to_string dep_node1.edges
                                in
                             FStar_String.concat ", " uu____5769  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5767
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1006_5780 = dep_node1  in
                           { edges = (uu___1006_5780.edges); color = Gray });
                        (let uu____5781 =
                           let uu____5792 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5792
                            in
                         match uu____5781 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1012_5828 = dep_node1  in
                                 {
                                   edges = (uu___1012_5828.edges);
                                   color = Black
                                 });
                              (let uu____5830 =
                                 FStar_Options.debug_at_level_no_module
                                   (FStar_Options.Other "Dep")
                                  in
                               if uu____5830
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5837 =
                                 let uu____5841 =
                                   FStar_List.collect
                                     (fun uu___14_5848  ->
                                        match uu___14_5848 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node1.edges
                                    in
                                 FStar_List.append uu____5841 all_friends1
                                  in
                               (uu____5837, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            let uu____5913 = all_friend_deps dep_graph [] ([], []) root_files
               in
            match uu____5913 with
            | (friends,all_files_0) ->
                ((let uu____5956 =
                    FStar_Options.debug_at_level_no_module
                      (FStar_Options.Other "Dep")
                     in
                  if uu____5956
                  then
                    let uu____5960 =
                      let uu____5962 =
                        FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                          friends
                         in
                      FStar_String.concat ", " uu____5962  in
                    FStar_Util.print3
                      "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                      (FStar_String.concat ", " all_files_0) uu____5960
                      (FStar_String.concat ", " interfaces_needing_inlining)
                  else ());
                 (let uu____5980 =
                    widen_deps friends dep_graph file_system_map widened  in
                  match uu____5980 with
                  | (widened1,dep_graph1) ->
                      let uu____5998 =
                        (let uu____6010 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep")
                            in
                         if uu____6010
                         then
                           FStar_Util.print_string
                             "==============Phase2==================\n"
                         else ());
                        all_friend_deps dep_graph1 [] ([], []) root_files  in
                      (match uu____5998 with
                       | (uu____6034,all_files) ->
                           ((let uu____6049 =
                               FStar_Options.debug_at_level_no_module
                                 (FStar_Options.Other "Dep")
                                in
                             if uu____6049
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
  fun file_system_map  ->
    fun dep_graph  ->
      fun interfaces_needing_inlining  ->
        fun for_extraction  ->
          (let uu____6096 =
             FStar_Options.debug_at_level_no_module
               (FStar_Options.Other "Dep")
              in
           if uu____6096
           then
             FStar_Util.print_string
               "==============Phase1==================\n"
           else ());
          (let widened = false  in
           let uu____6106 = (FStar_Options.cmi ()) && for_extraction  in
           if uu____6106
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
  fun file_system_map  ->
    fun dep_graph  ->
      fun interfaces_needing_inlining  ->
        fun root_files  ->
          fun for_extraction  ->
            let uu____6173 =
              phase1 file_system_map dep_graph interfaces_needing_inlining
                for_extraction
               in
            match uu____6173 with
            | (widened,dep_graph1) ->
                topological_dependences_of' file_system_map dep_graph1
                  interfaces_needing_inlining root_files widened
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
      (Prims.string Prims.list * deps))
  =
  fun all_cmd_line_files  ->
    fun get_parsing_data_from_cache  ->
      let all_cmd_line_files1 =
        FStar_All.pipe_right all_cmd_line_files
          (FStar_List.map
             (fun fn  ->
                let uu____6250 = FStar_Options.find_file fn  in
                match uu____6250 with
                | FStar_Pervasives_Native.None  ->
                    let uu____6256 =
                      let uu____6262 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____6262)
                       in
                    FStar_Errors.raise_err uu____6256
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____6292 =
          let uu____6296 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____6296  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6292  in
      let parse_results = FStar_Util.smap_create (Prims.of_int (40))  in
      let rec discover_one file_name1 =
        let uu____6363 =
          let uu____6365 = deps_try_find dep_graph file_name1  in
          uu____6365 = FStar_Pervasives_Native.None  in
        if uu____6363
        then
          let uu____6371 =
            let uu____6387 =
              let uu____6401 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____6401 file_name1  in
            match uu____6387 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None  ->
                let uu____6531 =
                  collect_one file_system_map file_name1
                    get_parsing_data_from_cache
                   in
                (match uu____6531 with
                 | (parsing_data1,deps1,needs_interface_inlining,additional_roots)
                     ->
                     (parsing_data1,
                       (deps1, additional_roots, needs_interface_inlining)))
             in
          match uu____6371 with
          | (parsing_data1,(deps1,mo_roots,needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name1
               else ();
               FStar_Util.smap_add parse_results file_name1 parsing_data1;
               (let deps2 =
                  let module_name1 = lowercase_module_name file_name1  in
                  let uu____6625 =
                    (is_implementation file_name1) &&
                      (has_interface file_system_map module_name1)
                     in
                  if uu____6625
                  then FStar_List.append deps1 [UseInterface module_name1]
                  else deps1  in
                let dep_node1 =
                  let uu____6633 = FStar_List.unique deps2  in
                  { edges = uu____6633; color = White }  in
                deps_add_dep dep_graph file_name1 dep_node1;
                (let uu____6635 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps2 mo_roots)
                    in
                 FStar_List.iter discover_one uu____6635)))
        else ()  in
      profile
        (fun uu____6645  -> FStar_List.iter discover_one all_cmd_line_files1)
        "FStar.Parser.Dep.discover";
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____6678 =
            let uu____6684 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____6684)  in
          FStar_Errors.raise_err uu____6678)
          in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let mo_files = FStar_Util.mk_ref []  in
         let rec aux cycle filename =
           let node =
             let uu____6736 = deps_try_find dep_graph1 filename  in
             match uu____6736 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____6740 =
                   FStar_Util.format1
                     "Impossible: Failed to find dependencies of %s" filename
                    in
                 failwith uu____6740
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____6754 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6754 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6765 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____6771 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6771 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6782 -> [x; UseImplementation f])
                     | uu____6786 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1133_6789 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____6791 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6791);
                deps_add_dep dep_graph1 filename
                  (let uu___1138_6802 = node  in
                   { edges = direct_deps; color = Black });
                (let uu____6803 = is_interface filename  in
                 if uu____6803
                 then
                   let uu____6806 =
                     let uu____6810 = lowercase_module_name filename  in
                     implementation_of_internal file_system_map1 uu____6810
                      in
                   FStar_Util.iter_opt uu____6806
                     (fun impl  ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu____6819 =
                            let uu____6823 = FStar_ST.op_Bang mo_files  in
                            impl :: uu____6823  in
                          FStar_ST.op_Colon_Equals mo_files uu____6819
                        else ())
                 else ()))
            in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu____6885 = FStar_ST.op_Bang mo_files  in
          FStar_List.iter (aux []) uu____6885)
          in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____6957 =
          profile
            (fun uu____6976  ->
               let uu____6977 =
                 let uu____6979 = FStar_Options.codegen ()  in
                 uu____6979 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____6977)
            "FStar.Parser.Dep.topological_dependences_of"
           in
        match uu____6957 with
        | (all_files,uu____6993) ->
            ((let uu____7003 =
                FStar_Options.debug_at_level_no_module
                  (FStar_Options.Other "Dep")
                 in
              if uu____7003
              then
                FStar_Util.print1 "Interfaces needing inlining: %s\n"
                  (FStar_String.concat ", " inlining_ifaces)
              else ());
             (all_files,
               (mk_deps dep_graph file_system_map all_cmd_line_files1
                  all_files inlining_ifaces parse_results)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun deps1  ->
    fun f  ->
      dependences_of deps1.file_system_map deps1.dep_graph
        deps1.cmd_line_files f
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____7057 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____7083  ->
              match uu____7083 with
              | (m,d) ->
                  let uu____7097 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____7097))
       in
    FStar_All.pipe_right uu____7057 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun deps1  ->
    let file_system_map = deps1.file_system_map  in
    let all_cmd_line_files = deps1.cmd_line_files  in
    let deps2 = deps1.dep_graph  in
    let keys = deps_keys deps2  in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun f  ->
            let dep_node1 =
              let uu____7132 = deps_try_find deps2 f  in
              FStar_All.pipe_right uu____7132 FStar_Option.get  in
            let files =
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                dep_node1.edges
               in
            let files1 =
              FStar_List.map (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                files
               in
            FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))
  
let (print_raw : deps -> unit) =
  fun deps1  ->
    let uu____7161 = deps1.dep_graph  in
    match uu____7161 with
    | Deps deps2 ->
        let uu____7165 =
          let uu____7167 =
            FStar_Util.smap_fold deps2
              (fun k  ->
                 fun dep_node1  ->
                   fun out  ->
                     let uu____7185 =
                       let uu____7187 =
                         let uu____7189 =
                           FStar_List.map dep_to_string dep_node1.edges  in
                         FStar_All.pipe_right uu____7189
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7187
                        in
                     uu____7185 :: out) []
             in
          FStar_All.pipe_right uu____7167 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____7165 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps1  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules = FStar_Util.smap_create (Prims.of_int (41))
         in
      let should_visit lc_module_name =
        (let uu____7261 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7261) ||
          (let uu____7268 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7268)
         in
      let mark_visiting lc_module_name =
        let ml_file_opt =
          FStar_Util.smap_try_find remaining_output_files lc_module_name  in
        FStar_Util.smap_remove remaining_output_files lc_module_name;
        FStar_Util.smap_add visited_other_modules lc_module_name true;
        ml_file_opt  in
      let emit_output_file_opt ml_file_opt =
        match ml_file_opt with
        | FStar_Pervasives_Native.None  -> ()
        | FStar_Pervasives_Native.Some ml_file ->
            let uu____7311 =
              let uu____7315 = FStar_ST.op_Bang order  in ml_file ::
                uu____7315
               in
            FStar_ST.op_Colon_Equals order uu____7311
         in
      let rec aux uu___15_7378 =
        match uu___15_7378 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name1 ->
                  let uu____7406 = deps_try_find deps1.dep_graph file_name1
                     in
                  (match uu____7406 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7409 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name1
                          in
                       failwith uu____7409
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7413;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7422 = should_visit lc_module_name  in
              if uu____7422
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7430 = implementation_of deps1 lc_module_name  in
                  visit_file uu____7430);
                 (let uu____7435 = interface_of deps1 lc_module_name  in
                  visit_file uu____7435);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7447 = FStar_ST.op_Bang order  in FStar_List.rev uu____7447)
       in
    let sb =
      let uu____7478 = FStar_BigInt.of_int_fs (Prims.of_int (10000))  in
      FStar_StringBuffer.create uu____7478  in
    let pr str =
      let uu____7488 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun uu____7489  -> ()) uu____7488  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps1.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7542 =
          let uu____7544 =
            let uu____7548 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7548  in
          FStar_Option.get uu____7544  in
        FStar_Util.replace_chars uu____7542 46 "_"  in
      let uu____7553 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____7553  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7575 = output_file ".ml" f  in norm_path uu____7575  in
    let output_krml_file f =
      let uu____7587 = output_file ".krml" f  in norm_path uu____7587  in
    let output_cmx_file f =
      let uu____7599 = output_file ".cmx" f  in norm_path uu____7599  in
    let cache_file f =
      let uu____7611 = cache_file_name f  in norm_path uu____7611  in
    let uu____7613 =
      phase1 deps1.file_system_map deps1.dep_graph
        deps1.interfaces_with_inlining true
       in
    match uu____7613 with
    | (widened,dep_graph) ->
        let all_checked_files =
          FStar_All.pipe_right keys
            (FStar_List.fold_left
               (fun all_checked_files  ->
                  fun file_name1  ->
                    let process_one_key uu____7655 =
                      let dep_node1 =
                        let uu____7657 =
                          deps_try_find deps1.dep_graph file_name1  in
                        FStar_All.pipe_right uu____7657 FStar_Option.get  in
                      let iface_deps =
                        let uu____7667 = is_interface file_name1  in
                        if uu____7667
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____7678 =
                             let uu____7682 =
                               lowercase_module_name file_name1  in
                             interface_of deps1 uu____7682  in
                           match uu____7678 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some iface ->
                               let uu____7694 =
                                 let uu____7697 =
                                   let uu____7698 =
                                     deps_try_find deps1.dep_graph iface  in
                                   FStar_Option.get uu____7698  in
                                 uu____7697.edges  in
                               FStar_Pervasives_Native.Some uu____7694)
                         in
                      let iface_deps1 =
                        FStar_Util.map_opt iface_deps
                          (FStar_List.filter
                             (fun iface_dep  ->
                                let uu____7715 =
                                  FStar_Util.for_some
                                    (dep_subsumed_by iface_dep)
                                    dep_node1.edges
                                   in
                                Prims.op_Negation uu____7715))
                         in
                      let norm_f = norm_path file_name1  in
                      let files =
                        FStar_List.map
                          (file_of_dep_aux true deps1.file_system_map
                             deps1.cmd_line_files) dep_node1.edges
                         in
                      let files1 =
                        match iface_deps1 with
                        | FStar_Pervasives_Native.None  -> files
                        | FStar_Pervasives_Native.Some iface_deps2 ->
                            let iface_files =
                              FStar_List.map
                                (file_of_dep_aux true deps1.file_system_map
                                   deps1.cmd_line_files) iface_deps2
                               in
                            FStar_Util.remove_dups
                              (fun x  -> fun y  -> x = y)
                              (FStar_List.append files iface_files)
                         in
                      let files2 = FStar_List.map norm_path files1  in
                      let files3 =
                        FStar_List.map
                          (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                          files2
                         in
                      let files4 = FStar_String.concat "\\\n\t" files3  in
                      let cache_file_name1 = cache_file file_name1  in
                      let all_checked_files1 =
                        let uu____7780 =
                          let uu____7782 =
                            let uu____7784 = module_name_of_file file_name1
                               in
                            FStar_Options.should_be_already_cached uu____7784
                             in
                          Prims.op_Negation uu____7782  in
                        if uu____7780
                        then
                          (print_entry cache_file_name1 norm_f files4;
                           cache_file_name1
                           ::
                           all_checked_files)
                        else all_checked_files  in
                      let uu____7794 =
                        let uu____7803 = FStar_Options.cmi ()  in
                        if uu____7803
                        then
                          profile
                            (fun uu____7824  ->
                               let uu____7825 = dep_graph_copy dep_graph  in
                               topological_dependences_of'
                                 deps1.file_system_map uu____7825
                                 deps1.interfaces_with_inlining [file_name1]
                                 widened)
                            "FStar.Parser.Dep.topological_dependences_of_2"
                        else
                          (let maybe_widen_deps f_deps =
                             FStar_List.map
                               (fun dep  ->
                                  file_of_dep_aux false deps1.file_system_map
                                    deps1.cmd_line_files dep) f_deps
                              in
                           let fst_files = maybe_widen_deps dep_node1.edges
                              in
                           let fst_files_from_iface =
                             match iface_deps1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some iface_deps2 ->
                                 maybe_widen_deps iface_deps2
                              in
                           let uu____7863 =
                             FStar_Util.remove_dups
                               (fun x  -> fun y  -> x = y)
                               (FStar_List.append fst_files
                                  fst_files_from_iface)
                              in
                           (uu____7863, false))
                         in
                      match uu____7794 with
                      | (all_fst_files_dep,widened1) ->
                          let all_checked_fst_dep_files =
                            FStar_All.pipe_right all_fst_files_dep
                              (FStar_List.map cache_file)
                             in
                          let all_checked_fst_dep_files_string =
                            FStar_String.concat " \\\n\t"
                              all_checked_fst_dep_files
                             in
                          ((let uu____7910 = is_implementation file_name1  in
                            if uu____7910
                            then
                              ((let uu____7914 =
                                  (FStar_Options.cmi ()) && widened1  in
                                if uu____7914
                                then
                                  ((let uu____7918 =
                                      output_ml_file file_name1  in
                                    print_entry uu____7918 cache_file_name1
                                      all_checked_fst_dep_files_string);
                                   (let uu____7920 =
                                      output_krml_file file_name1  in
                                    print_entry uu____7920 cache_file_name1
                                      all_checked_fst_dep_files_string))
                                else
                                  ((let uu____7925 =
                                      output_ml_file file_name1  in
                                    print_entry uu____7925 cache_file_name1
                                      "");
                                   (let uu____7928 =
                                      output_krml_file file_name1  in
                                    print_entry uu____7928 cache_file_name1
                                      "")));
                               (let cmx_files =
                                  let extracted_fst_files =
                                    FStar_All.pipe_right all_fst_files_dep
                                      (FStar_List.filter
                                         (fun df  ->
                                            (let uu____7953 =
                                               lowercase_module_name df  in
                                             let uu____7955 =
                                               lowercase_module_name
                                                 file_name1
                                                in
                                             uu____7953 <> uu____7955) &&
                                              (let uu____7959 =
                                                 lowercase_module_name df  in
                                               FStar_Options.should_extract
                                                 uu____7959)))
                                     in
                                  FStar_All.pipe_right extracted_fst_files
                                    (FStar_List.map output_cmx_file)
                                   in
                                let uu____7969 =
                                  let uu____7971 =
                                    lowercase_module_name file_name1  in
                                  FStar_Options.should_extract uu____7971  in
                                if uu____7969
                                then
                                  let cmx_files1 =
                                    FStar_String.concat "\\\n\t" cmx_files
                                     in
                                  let uu____7977 = output_cmx_file file_name1
                                     in
                                  let uu____7979 = output_ml_file file_name1
                                     in
                                  print_entry uu____7977 uu____7979
                                    cmx_files1
                                else ()))
                            else
                              (let uu____7985 =
                                 (let uu____7989 =
                                    let uu____7991 =
                                      lowercase_module_name file_name1  in
                                    has_implementation deps1.file_system_map
                                      uu____7991
                                     in
                                  Prims.op_Negation uu____7989) &&
                                   (is_interface file_name1)
                                  in
                               if uu____7985
                               then
                                 let uu____7994 =
                                   (FStar_Options.cmi ()) &&
                                     (widened1 || true)
                                    in
                                 (if uu____7994
                                  then
                                    let uu____7998 =
                                      output_krml_file file_name1  in
                                    print_entry uu____7998 cache_file_name1
                                      all_checked_fst_dep_files_string
                                  else
                                    (let uu____8002 =
                                       output_krml_file file_name1  in
                                     print_entry uu____8002 cache_file_name1
                                       ""))
                               else ()));
                           all_checked_files1)
                       in
                    profile process_one_key
                      "FStar.Parser.Dep.process_one_key") [])
           in
        let all_fst_files =
          let uu____8016 =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation)
             in
          FStar_All.pipe_right uu____8016
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_fsti_files =
          let uu____8038 =
            FStar_All.pipe_right keys (FStar_List.filter is_interface)  in
          FStar_All.pipe_right uu____8038
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.of_int (41))  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8079 = FStar_Options.should_extract mname  in
                  if uu____8079
                  then
                    let uu____8082 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____8082
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.of_int (41))  in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8109 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____8109));
          sort_output_files krml_file_map  in
        let print_all tag files =
          pr tag;
          pr "=\\\n\t";
          FStar_List.iter (fun f  -> pr (norm_path f); pr " \\\n\t") files;
          pr "\n"  in
        (print_all "ALL_FST_FILES" all_fst_files;
         print_all "ALL_FSTI_FILES" all_fsti_files;
         print_all "ALL_CHECKED_FILES" all_checked_files;
         print_all "ALL_ML_FILES" all_ml_files;
         print_all "ALL_KRML_FILES" all_krml_files;
         FStar_StringBuffer.output_channel FStar_Util.stdout sb)
  
let (print : deps -> unit) =
  fun deps1  ->
    let uu____8159 = FStar_Options.dep ()  in
    match uu____8159 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps1
    | FStar_Pervasives_Native.Some "full" ->
        profile (fun uu____8168  -> print_full deps1)
          "FStar.Parser.Deps.print_full_deps"
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps1.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps1
    | FStar_Pervasives_Native.Some uu____8174 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  
let (print_fsmap :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap -> Prims.string)
  =
  fun fsmap  ->
    FStar_Util.smap_fold fsmap
      (fun k  ->
         fun uu____8229  ->
           fun s  ->
             match uu____8229 with
             | (v0,v1) ->
                 let uu____8258 =
                   let uu____8260 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____8260  in
                 FStar_String.op_Hat s uu____8258) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps1  ->
    fun module_name1  ->
      let uu____8281 =
        let uu____8283 = FStar_Ident.string_of_lid module_name1  in
        FStar_String.lowercase uu____8283  in
      has_interface deps1.file_system_map uu____8281
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps1  ->
    fun module_name1  ->
      let m =
        let uu____8299 = FStar_Ident.string_of_lid module_name1  in
        FStar_String.lowercase uu____8299  in
      FStar_All.pipe_right deps1.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8310 =
                   let uu____8312 = module_name_of_file f  in
                   FStar_String.lowercase uu____8312  in
                 uu____8310 = m)))
  