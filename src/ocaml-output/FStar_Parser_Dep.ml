open Prims
let profile : 'Auu____16 . (unit -> 'Auu____16) -> Prims.string -> 'Auu____16
  =
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
  'Auu____262 .
    'Auu____262 FStar_Pervasives_Native.option -> 'Auu____262 Prims.list
  =
  fun uu___0_271  ->
    match uu___0_271 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____280 .
    ('Auu____280 FStar_Pervasives_Native.option * 'Auu____280
      FStar_Pervasives_Native.option) -> 'Auu____280 Prims.list
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
let empty_dependences : 'Auu____519 . unit -> 'Auu____519 Prims.list =
  fun uu____522  -> [] 
type dep_node = {
  edges: dependences ;
  color: color }
let (__proj__Mkdep_node__item__edges : dep_node -> dependences) =
  fun projectee  -> match projectee with | { edges; color;_} -> edges 
let (__proj__Mkdep_node__item__color : dep_node -> color) =
  fun projectee  -> match projectee with | { edges; color;_} -> color 
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
    match projectee with | P_begin_module _0 -> true | uu____635 -> false
  
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_begin_module _0 -> _0 
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_open _0 -> true | uu____659 -> false
  
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_open _0 -> _0 
let (uu___is_P_open_module_or_namespace : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_open_module_or_namespace _0 -> true
    | uu____697 -> false
  
let (__proj__P_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStar_Ident.lid)) =
  fun projectee  ->
    match projectee with | P_open_module_or_namespace _0 -> _0
  
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_dep _0 -> true | uu____733 -> false
  
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_dep _0 -> _0 
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_alias _0 -> true | uu____771 -> false
  
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_alias _0 -> _0 
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_lid _0 -> true | uu____802 -> false
  
let (__proj__P_lid__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_lid _0 -> _0 
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_inline_for_extraction  -> true
    | uu____820 -> false
  
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee  -> match projectee with | Mk_pd _0 -> _0 
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt  ->
    let str_of_open_kind uu___2_863 =
      match uu___2_863 with
      | Open_module  -> "P_open_module"
      | Open_namespace  -> "P_open_namespace"  in
    match elt with
    | P_begin_module lid ->
        let uu____869 =
          let uu____871 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____871 ")"  in
        FStar_String.op_Hat "P_begin_module (" uu____869
    | P_open (b,lid) ->
        let uu____879 =
          let uu____881 = FStar_Util.string_of_bool b  in
          let uu____883 =
            let uu____885 =
              let uu____887 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____887 ")"  in
            FStar_String.op_Hat ", " uu____885  in
          FStar_String.op_Hat uu____881 uu____883  in
        FStar_String.op_Hat "P_open (" uu____879
    | P_open_module_or_namespace (k,lid) ->
        let uu____894 =
          let uu____896 =
            let uu____898 =
              let uu____900 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____900 ")"  in
            FStar_String.op_Hat ", " uu____898  in
          FStar_String.op_Hat (str_of_open_kind k) uu____896  in
        FStar_String.op_Hat "P_open_module_or_namespace (" uu____894
    | P_dep (b,lid) ->
        let uu____909 =
          let uu____911 = FStar_Ident.text_of_lid lid  in
          let uu____913 =
            let uu____915 =
              let uu____917 = FStar_Util.string_of_bool b  in
              FStar_String.op_Hat uu____917 ")"  in
            FStar_String.op_Hat ", " uu____915  in
          FStar_String.op_Hat uu____911 uu____913  in
        FStar_String.op_Hat "P_dep (" uu____909
    | P_alias (id1,lid) ->
        let uu____924 =
          let uu____926 = FStar_Ident.text_of_id id1  in
          let uu____928 =
            let uu____930 =
              let uu____932 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____932 ")"  in
            FStar_String.op_Hat ", " uu____930  in
          FStar_String.op_Hat uu____926 uu____928  in
        FStar_String.op_Hat "P_alias (" uu____924
    | P_lid lid ->
        let uu____938 =
          let uu____940 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____940 ")"  in
        FStar_String.op_Hat "P_lid (" uu____938
    | P_inline_for_extraction  -> "P_inline_for_extraction"
  
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___3_951  ->
    match uu___3_951 with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s  ->
                fun elt  ->
                  let uu____966 =
                    let uu____968 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt  in
                    FStar_String.op_Hat "; " uu____968  in
                  FStar_String.op_Hat s uu____966) "")
  
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
          (let uu____1018 = FStar_Ident.text_of_id i1  in
           let uu____1020 = FStar_Ident.text_of_id i2  in
           uu____1018 = uu____1020) && (FStar_Ident.lid_equals l1 l2)
      | (P_lid l1,P_lid l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction ,P_inline_for_extraction ) -> true
      | (uu____1026,uu____1027) -> false
  
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
  fun uu____1243  ->
    fun k  -> match uu____1243 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____1265  ->
    fun k  ->
      fun v1  -> match uu____1265 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____1280  -> match uu____1280 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____1292  ->
    let uu____1293 = FStar_Util.smap_create (Prims.of_int (41))  in
    Deps uu____1293
  
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
  let uu____1351 = deps_empty ()  in
  let uu____1352 = FStar_Util.smap_create Prims.int_zero  in
  let uu____1364 = FStar_Util.smap_create Prims.int_zero  in
  mk_deps uu____1351 uu____1352 [] [] [] uu____1364 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___4_1377  ->
    match uu___4_1377 with
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
      let uu____1406 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1406 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1433) ->
          let uu____1455 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1455
      | FStar_Pervasives_Native.Some
          (uu____1458,FStar_Pervasives_Native.Some fn) ->
          let uu____1481 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1481
      | uu____1484 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1517 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1517 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1544) ->
          FStar_Pervasives_Native.Some iface
      | uu____1567 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1600 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1600 with
      | FStar_Pervasives_Native.Some
          (uu____1626,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1650 -> FStar_Pervasives_Native.None
  
let (interface_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps  -> fun key  -> interface_of_internal deps.file_system_map key 
let (implementation_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps  ->
    fun key  -> implementation_of_internal deps.file_system_map key
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1711 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1711
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1731 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1731
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1766 =
      let uu____1770 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1770  in
    match uu____1766 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1781 =
            ((let uu____1785 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1785) &&
               (let uu____1791 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1791))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1794 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1794))
             in
          if uu____1781
          then
            let uu____1797 =
              let uu____1803 =
                let uu____1805 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expect %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1805
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1803)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1797
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1812 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1812
        then
          let uu____1818 =
            let uu____1824 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1824)
             in
          FStar_Errors.raise_err uu____1818
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.of_int (100))  in
  let memo1 f x =
    let uu____1860 = FStar_Util.smap_try_find memo x  in
    match uu____1860 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1887 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1887 FStar_Util.must
  
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
                      (let uu____1941 = lowercase_module_name fn  in
                       key = uu____1941)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1960 = interface_of_internal file_system_map key  in
              (match uu____1960 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1967 =
                     let uu____1973 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1973)  in
                   FStar_Errors.raise_err uu____1967
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1983 =
                (cmd_line_has_impl key) &&
                  (let uu____1986 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1986)
                 in
              if uu____1983
              then
                let uu____1993 = FStar_Options.expose_interfaces ()  in
                (if uu____1993
                 then
                   let uu____1997 =
                     let uu____1999 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____1999  in
                   maybe_use_cache_of uu____1997
                 else
                   (let uu____2006 =
                      let uu____2012 =
                        let uu____2014 =
                          let uu____2016 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____2016  in
                        let uu____2021 =
                          let uu____2023 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____2023  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____2014 uu____2021
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____2012)
                       in
                    FStar_Errors.raise_err uu____2006))
              else
                (let uu____2033 =
                   let uu____2035 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____2035  in
                 maybe_use_cache_of uu____2033)
          | PreferInterface key ->
              let uu____2042 = implementation_of_internal file_system_map key
                 in
              (match uu____2042 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2048 =
                     let uu____2054 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2054)
                      in
                   FStar_Errors.raise_err uu____2048
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____2064 = implementation_of_internal file_system_map key
                 in
              (match uu____2064 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2070 =
                     let uu____2076 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2076)
                      in
                   FStar_Errors.raise_err uu____2070
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____2086 = implementation_of_internal file_system_map key
                 in
              (match uu____2086 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2092 =
                     let uu____2098 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2098)
                      in
                   FStar_Errors.raise_err uu____2092
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
    fun deps  ->
      fun all_cmd_line_files  ->
        fun fn  ->
          let uu____2159 = deps_try_find deps fn  in
          match uu____2159 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____2167;_} ->
              let uu____2168 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files) deps1
                 in
              FStar_All.pipe_right uu____2168
                (FStar_List.filter (fun k  -> k <> fn))
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____2196 =
       let uu____2198 =
         let uu____2200 =
           let uu____2202 =
             let uu____2206 =
               let uu____2210 = deps_keys graph  in
               FStar_List.unique uu____2210  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____2224 =
                      let uu____2225 = deps_try_find graph k  in
                      FStar_Util.must uu____2225  in
                    uu____2224.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____2246 =
                      let uu____2248 = lowercase_module_name k  in
                      r uu____2248  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2246
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____2206
              in
           FStar_String.concat "\n" uu____2202  in
         FStar_String.op_Hat uu____2200 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____2198  in
     FStar_Util.write_file "dep.graph" uu____2196)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____2269  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____2295 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____2295  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____2335 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____2335
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____2372 =
              let uu____2378 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____2378)  in
            FStar_Errors.raise_err uu____2372)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.of_int (41))  in
    let add_entry key full_path =
      let uu____2441 = FStar_Util.smap_try_find map1 key  in
      match uu____2441 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2488 = is_interface full_path  in
          if uu____2488
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2537 = is_interface full_path  in
          if uu____2537
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2579 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2597  ->
          match uu____2597 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2579);
    FStar_List.iter
      (fun f  ->
         let uu____2616 = lowercase_module_name f  in add_entry uu____2616 f)
      filenames;
    map1
  
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool)
  =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false  in
        let prefix2 = FStar_String.op_Hat prefix1 "."  in
        FStar_Util.smap_iter original_map
          (fun k  ->
             fun uu____2664  ->
               if FStar_Util.starts_with k prefix2
               then
                 let suffix =
                   FStar_String.substring k (FStar_String.length prefix2)
                     ((FStar_String.length k) - (FStar_String.length prefix2))
                    in
                 let filename =
                   let uu____2690 = FStar_Util.smap_try_find original_map k
                      in
                   FStar_Util.must uu____2690  in
                 (FStar_Util.smap_add working_map suffix filename;
                  FStar_ST.op_Colon_Equals found true)
               else ());
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2810 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2810 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2833 = string_of_lid l last1  in
      FStar_String.lowercase uu____2833
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2842 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2842
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2864 =
        let uu____2866 =
          let uu____2868 =
            let uu____2870 =
              let uu____2874 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2874  in
            FStar_Util.must uu____2870  in
          FStar_String.lowercase uu____2868  in
        uu____2866 <> k'  in
      if uu____2864
      then
        let uu____2879 = FStar_Ident.range_of_lid lid  in
        let uu____2880 =
          let uu____2886 =
            let uu____2888 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2888 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2886)  in
        FStar_Errors.log_issue uu____2879 uu____2880
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2904 -> false
  
let (core_modules : Prims.string Prims.list) =
  let uu____2910 =
    let uu____2914 = FStar_Options.prims_basename ()  in
    let uu____2916 =
      let uu____2920 = FStar_Options.pervasives_basename ()  in
      let uu____2922 =
        let uu____2926 = FStar_Options.pervasives_native_basename ()  in
        [uu____2926]  in
      uu____2920 :: uu____2922  in
    uu____2914 :: uu____2916  in
  FStar_All.pipe_right uu____2910 (FStar_List.map module_name_of_file) 
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let uu____2956 =
      let uu____2958 = module_name_of_file filename  in
      FStar_List.mem uu____2958 core_modules  in
    if uu____2956
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2997 =
         let uu____3000 = lowercase_module_name full_filename  in
         namespace_of_module uu____3000  in
       match uu____2997 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____3039 -> d = d'
  
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
          let deps = FStar_Util.mk_ref []  in
          let has_inline_for_extraction = FStar_Util.mk_ref false  in
          let mo_roots =
            let mname = lowercase_module_name filename1  in
            let uu____3157 =
              (is_interface filename1) &&
                (has_implementation original_map1 mname)
               in
            if uu____3157 then [UseImplementation mname] else []  in
          let auto_open =
            let uu____3167 = hard_coded_dependencies filename1  in
            FStar_All.pipe_right uu____3167
              (FStar_List.map
                 (fun uu____3189  ->
                    match uu____3189 with
                    | (lid,k) -> P_open_module_or_namespace (k, lid)))
             in
          let working_map = FStar_Util.smap_copy original_map1  in
          let set_interface_inlining uu____3224 =
            let uu____3225 = is_interface filename1  in
            if uu____3225
            then FStar_ST.op_Colon_Equals has_inline_for_extraction true
            else ()  in
          let add_dep deps1 d =
            let uu____3347 =
              let uu____3349 =
                let uu____3351 = FStar_ST.op_Bang deps1  in
                FStar_List.existsML (dep_subsumed_by d) uu____3351  in
              Prims.op_Negation uu____3349  in
            if uu____3347
            then
              let uu____3378 =
                let uu____3381 = FStar_ST.op_Bang deps1  in d :: uu____3381
                 in
              FStar_ST.op_Colon_Equals deps1 uu____3378
            else ()  in
          let dep_edge module_name is_friend =
            if is_friend
            then FriendImplementation module_name
            else PreferInterface module_name  in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true  in
            let uu____3472 = resolve_module_name original_or_working_map key
               in
            match uu____3472 with
            | FStar_Pervasives_Native.Some module_name ->
                (add_dep deps (dep_edge module_name is_friend); true)
            | uu____3482 -> false  in
          let record_open_module let_open lid =
            let uu____3501 =
              (let_open && (add_dependence_edge working_map lid false)) ||
                ((Prims.op_Negation let_open) &&
                   (add_dependence_edge original_map1 lid false))
               in
            if uu____3501
            then true
            else
              (if let_open
               then
                 (let uu____3512 = FStar_Ident.range_of_lid lid  in
                  let uu____3513 =
                    let uu____3519 =
                      let uu____3521 = string_of_lid lid true  in
                      FStar_Util.format1 "Module not found: %s" uu____3521
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3519)
                     in
                  FStar_Errors.log_issue uu____3512 uu____3513)
               else ();
               false)
             in
          let record_open_namespace lid =
            let key = lowercase_join_longident lid true  in
            let r = enter_namespace original_map1 working_map key  in
            if Prims.op_Negation r
            then
              let uu____3541 = FStar_Ident.range_of_lid lid  in
              let uu____3542 =
                let uu____3548 =
                  let uu____3550 = string_of_lid lid true  in
                  FStar_Util.format1
                    "No modules in namespace %s and no file with that name either"
                    uu____3550
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3548)
                 in
              FStar_Errors.log_issue uu____3541 uu____3542
            else ()  in
          let record_open let_open lid =
            let uu____3570 = record_open_module let_open lid  in
            if uu____3570
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid
              else ()
             in
          let record_open_module_or_namespace uu____3587 =
            match uu____3587 with
            | (lid,kind) ->
                (match kind with
                 | Open_namespace  -> record_open_namespace lid
                 | Open_module  ->
                     let uu____3594 = record_open_module false lid  in ())
             in
          let record_module_alias ident lid =
            let key =
              let uu____3611 = FStar_Ident.text_of_id ident  in
              FStar_String.lowercase uu____3611  in
            let alias = lowercase_join_longident lid true  in
            let uu____3616 = FStar_Util.smap_try_find original_map1 alias  in
            match uu____3616 with
            | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                (FStar_Util.smap_add working_map key deps_of_aliased_module;
                 (let uu____3673 =
                    let uu____3674 = lowercase_join_longident lid true  in
                    dep_edge uu____3674 false  in
                  add_dep deps uu____3673);
                 true)
            | FStar_Pervasives_Native.None  ->
                ((let uu____3690 = FStar_Ident.range_of_lid lid  in
                  let uu____3691 =
                    let uu____3697 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3697)
                     in
                  FStar_Errors.log_issue uu____3690 uu____3691);
                 false)
             in
          let add_dep_on_module module_name is_friend =
            let uu____3715 =
              add_dependence_edge working_map module_name is_friend  in
            if uu____3715
            then ()
            else
              (let uu____3720 =
                 FStar_Options.debug_at_level_no_module
                   (FStar_Options.Other "Dep")
                  in
               if uu____3720
               then
                 let uu____3724 = FStar_Ident.range_of_lid module_name  in
                 let uu____3725 =
                   let uu____3731 =
                     let uu____3733 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____3733
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____3731)
                    in
                 FStar_Errors.log_issue uu____3724 uu____3725
               else ())
             in
          let record_lid lid =
            match lid.FStar_Ident.ns with
            | [] -> ()
            | uu____3745 ->
                let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                   in
                add_dep_on_module module_name false
             in
          let begin_module lid =
            if (FStar_List.length lid.FStar_Ident.ns) > Prims.int_zero
            then
              let uu____3758 =
                let uu____3760 = namespace_of_lid lid  in
                enter_namespace original_map1 working_map uu____3760  in
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
                       | P_alias (id1,lid) ->
                           let uu____3786 = record_module_alias id1 lid  in
                           ()
                       | P_lid lid -> record_lid lid
                       | P_inline_for_extraction  ->
                           set_interface_inlining ())));
          (let uu____3789 = FStar_ST.op_Bang deps  in
           let uu____3815 = FStar_ST.op_Bang has_inline_for_extraction  in
           (uu____3789, uu____3815, mo_roots))
           in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____3849 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____3849
        then
          ((let uu____3869 =
              FStar_Options.debug_at_level_no_module
                (FStar_Options.Other "Dep")
               in
            if uu____3869
            then
              FStar_Util.print1
                "Reading the parsing data for %s from its checked file\n"
                filename
            else ());
           (let uu____3876 =
              let uu____3888 =
                FStar_All.pipe_right data_from_cache FStar_Util.must  in
              from_parsing_data uu____3888 original_map filename  in
            match uu____3876 with
            | (deps,has_inline_for_extraction,mo_roots) ->
                let uu____3917 =
                  FStar_All.pipe_right data_from_cache FStar_Util.must  in
                (uu____3917, deps, has_inline_for_extraction, mo_roots)))
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref Prims.int_zero  in
           let pd = FStar_Util.mk_ref []  in
           let add_to_parsing_data elt =
             let uu____3946 =
               let uu____3948 =
                 let uu____3950 = FStar_ST.op_Bang pd  in
                 FStar_List.existsML (fun e  -> parsing_data_elt_eq e elt)
                   uu____3950
                  in
               Prims.op_Negation uu____3948  in
             if uu____3946
             then
               let uu____3979 =
                 let uu____3982 = FStar_ST.op_Bang pd  in elt :: uu____3982
                  in
               FStar_ST.op_Colon_Equals pd uu____3979
             else ()  in
           let rec collect_module uu___5_4139 =
             match uu___5_4139 with
             | FStar_Parser_AST.Module (lid,decls) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
             | FStar_Parser_AST.Interface (lid,decls,uu____4150) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
           
           and collect_decls decls =
             FStar_List.iter
               (fun x  ->
                  collect_decl x.FStar_Parser_AST.d;
                  FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                  (match x.FStar_Parser_AST.d with
                   | FStar_Parser_AST.Val uu____4169 when
                       FStar_List.contains
                         FStar_Parser_AST.Inline_for_extraction
                         x.FStar_Parser_AST.quals
                       -> add_to_parsing_data P_inline_for_extraction
                   | uu____4174 -> ())) decls
           
           and collect_decl d =
             match d with
             | FStar_Parser_AST.Include lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Open lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Friend lid ->
                 let uu____4183 =
                   let uu____4184 =
                     let uu____4190 =
                       let uu____4191 = lowercase_join_longident lid true  in
                       FStar_All.pipe_right uu____4191 FStar_Ident.lid_of_str
                        in
                     (true, uu____4190)  in
                   P_dep uu____4184  in
                 add_to_parsing_data uu____4183
             | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStar_Parser_AST.TopLevelLet (uu____4199,patterms) ->
                 FStar_List.iter
                   (fun uu____4221  ->
                      match uu____4221 with
                      | (pat,t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStar_Parser_AST.Main t -> collect_term t
             | FStar_Parser_AST.Splice (uu____4230,t) -> collect_term t
             | FStar_Parser_AST.Assume (uu____4236,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4238;
                   FStar_Parser_AST.mdest = uu____4239;
                   FStar_Parser_AST.lift_op =
                     FStar_Parser_AST.NonReifiableLift t;_}
                 -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4241;
                   FStar_Parser_AST.mdest = uu____4242;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                 -> collect_term t
             | FStar_Parser_AST.Val (uu____4244,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4246;
                   FStar_Parser_AST.mdest = uu____4247;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                     (t0,t1);_}
                 -> (collect_term t0; collect_term t1)
             | FStar_Parser_AST.Tycon (uu____4251,tc,ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStar_Parser_Const.mk_class_lid)
                  else ();
                  FStar_List.iter collect_tycon ts)
             | FStar_Parser_AST.Exception (uu____4266,t) ->
                 FStar_Util.iter_opt t collect_term
             | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.LayeredEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.Polymonadic_bind
                 (uu____4274,uu____4275,uu____4276,bind1) ->
                 collect_term bind1
             | FStar_Parser_AST.Pragma uu____4278 -> ()
             | FStar_Parser_AST.TopLevelModule lid ->
                 (FStar_Util.incr num_of_toplevelmods;
                  (let uu____4281 =
                     let uu____4283 = FStar_ST.op_Bang num_of_toplevelmods
                        in
                     uu____4283 > Prims.int_one  in
                   if uu____4281
                   then
                     let uu____4308 =
                       let uu____4314 =
                         let uu____4316 = string_of_lid lid true  in
                         FStar_Util.format1
                           "Automatic dependency analysis demands one module per file (module %s not supported)"
                           uu____4316
                          in
                       (FStar_Errors.Fatal_OneModulePerFile, uu____4314)  in
                     let uu____4321 = FStar_Ident.range_of_lid lid  in
                     FStar_Errors.raise_error uu____4308 uu____4321
                   else ()))
           
           and collect_tycon uu___6_4324 =
             match uu___6_4324 with
             | FStar_Parser_AST.TyconAbstract (uu____4325,binders,k) ->
                 (collect_binders binders; FStar_Util.iter_opt k collect_term)
             | FStar_Parser_AST.TyconAbbrev (uu____4337,binders,k,t) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  collect_term t)
             | FStar_Parser_AST.TyconRecord (uu____4351,binders,k,identterms)
                 ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4384  ->
                       match uu____4384 with
                       | (uu____4389,t) -> collect_term t) identterms)
             | FStar_Parser_AST.TyconVariant
                 (uu____4391,binders,k,identterms) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4440  ->
                       match uu____4440 with
                       | (uu____4450,t,uu____4452) ->
                           FStar_Util.iter_opt t collect_term) identterms)
           
           and collect_effect_decl uu___7_4459 =
             match uu___7_4459 with
             | FStar_Parser_AST.DefineEffect (uu____4460,binders,t,decls) ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStar_Parser_AST.RedefineEffect (uu____4474,binders,t) ->
                 (collect_binders binders; collect_term t)
           
           and collect_binders binders =
             FStar_List.iter collect_binder binders
           
           and collect_binder b =
             collect_aqual b.FStar_Parser_AST.aqual;
             (match b with
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                    (uu____4487,t);
                  FStar_Parser_AST.brange = uu____4489;
                  FStar_Parser_AST.blevel = uu____4490;
                  FStar_Parser_AST.aqual = uu____4491;_} -> collect_term t
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                    (uu____4494,t);
                  FStar_Parser_AST.brange = uu____4496;
                  FStar_Parser_AST.blevel = uu____4497;
                  FStar_Parser_AST.aqual = uu____4498;_} -> collect_term t
              | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu____4502;
                  FStar_Parser_AST.blevel = uu____4503;
                  FStar_Parser_AST.aqual = uu____4504;_} -> collect_term t
              | uu____4507 -> ())
           
           and collect_aqual uu___8_4508 =
             match uu___8_4508 with
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                 collect_term t
             | uu____4512 -> ()
           
           and collect_term t = collect_term' t.FStar_Parser_AST.tm
           
           and collect_constant uu___9_4516 =
             match uu___9_4516 with
             | FStar_Const.Const_int
                 (uu____4517,FStar_Pervasives_Native.Some (signedness,width))
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
                 let uu____4544 =
                   let uu____4545 =
                     let uu____4551 =
                       let uu____4552 =
                         FStar_Util.format2 "fstar.%sint%s" u w  in
                       FStar_All.pipe_right uu____4552 FStar_Ident.lid_of_str
                        in
                     (false, uu____4551)  in
                   P_dep uu____4545  in
                 add_to_parsing_data uu____4544
             | FStar_Const.Const_char uu____4558 ->
                 let uu____4560 =
                   let uu____4561 =
                     let uu____4567 =
                       FStar_All.pipe_right "fstar.char"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4567)  in
                   P_dep uu____4561  in
                 add_to_parsing_data uu____4560
             | FStar_Const.Const_float uu____4572 ->
                 let uu____4573 =
                   let uu____4574 =
                     let uu____4580 =
                       FStar_All.pipe_right "fstar.float"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4580)  in
                   P_dep uu____4574  in
                 add_to_parsing_data uu____4573
             | uu____4585 -> ()
           
           and collect_term' uu___12_4586 =
             match uu___12_4586 with
             | FStar_Parser_AST.Wild  -> ()
             | FStar_Parser_AST.Const c -> collect_constant c
             | FStar_Parser_AST.Op (s,ts) ->
                 ((let uu____4595 =
                     let uu____4597 = FStar_Ident.text_of_id s  in
                     uu____4597 = "@"  in
                   if uu____4595
                   then
                     let uu____4602 =
                       let uu____4603 =
                         let uu____4604 =
                           FStar_Ident.path_of_text
                             "FStar.List.Tot.Base.append"
                            in
                         FStar_Ident.lid_of_path uu____4604
                           FStar_Range.dummyRange
                          in
                       FStar_Parser_AST.Name uu____4603  in
                     collect_term' uu____4602
                   else ());
                  FStar_List.iter collect_term ts)
             | FStar_Parser_AST.Tvar uu____4608 -> ()
             | FStar_Parser_AST.Uvar uu____4609 -> ()
             | FStar_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Projector (lid,uu____4612) ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Construct (lid,termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStar_List.iter
                    (fun uu____4637  ->
                       match uu____4637 with
                       | (t,uu____4643) -> collect_term t) termimps)
             | FStar_Parser_AST.Abs (pats,t) ->
                 (collect_patterns pats; collect_term t)
             | FStar_Parser_AST.App (t1,t2,uu____4653) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Let (uu____4655,patterms,t) ->
                 (FStar_List.iter
                    (fun uu____4705  ->
                       match uu____4705 with
                       | (attrs_opt,(pat,t1)) ->
                           ((let uu____4734 =
                               FStar_Util.map_opt attrs_opt
                                 (FStar_List.iter collect_term)
                                in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStar_Parser_AST.LetOpen (lid,t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStar_Parser_AST.Bind (uu____4745,t1,t2) ->
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
                    (fun uu____4841  ->
                       match uu____4841 with
                       | (uu____4846,t1) -> collect_term t1) idterms)
             | FStar_Parser_AST.Project (t,uu____4849) -> collect_term t
             | FStar_Parser_AST.Product (binders,t) ->
                 (collect_binders binders; collect_term t)
             | FStar_Parser_AST.Sum (binders,t) ->
                 (FStar_List.iter
                    (fun uu___10_4878  ->
                       match uu___10_4878 with
                       | FStar_Util.Inl b -> collect_binder b
                       | FStar_Util.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStar_Parser_AST.QForall (binders,(uu____4886,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.QExists (binders,(uu____4920,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.Refine (binder,t) ->
                 (collect_binder binder; collect_term t)
             | FStar_Parser_AST.NamedTyp (uu____4956,t) -> collect_term t
             | FStar_Parser_AST.Paren t -> collect_term t
             | FStar_Parser_AST.Requires (t,uu____4960) -> collect_term t
             | FStar_Parser_AST.Ensures (t,uu____4968) -> collect_term t
             | FStar_Parser_AST.Labeled (t,uu____4976,uu____4977) ->
                 collect_term t
             | FStar_Parser_AST.Quote (t,uu____4983) -> collect_term t
             | FStar_Parser_AST.Antiquote t -> collect_term t
             | FStar_Parser_AST.VQuote t -> collect_term t
             | FStar_Parser_AST.Attributes cattributes ->
                 FStar_List.iter collect_term cattributes
             | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                 ((let uu____4997 =
                     let uu____4998 =
                       let uu____5004 = FStar_Ident.lid_of_str "FStar.Calc"
                          in
                       (false, uu____5004)  in
                     P_dep uu____4998  in
                   add_to_parsing_data uu____4997);
                  collect_term rel;
                  collect_term init1;
                  FStar_List.iter
                    (fun uu___11_5016  ->
                       match uu___11_5016 with
                       | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
           
           and collect_patterns ps = FStar_List.iter collect_pattern ps
           
           and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
           
           and collect_pattern' uu___13_5026 =
             match uu___13_5026 with
             | FStar_Parser_AST.PatVar (uu____5027,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatTvar (uu____5033,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
             | FStar_Parser_AST.PatOp uu____5042 -> ()
             | FStar_Parser_AST.PatConst uu____5043 -> ()
             | FStar_Parser_AST.PatApp (p,ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStar_Parser_AST.PatName uu____5051 -> ()
             | FStar_Parser_AST.PatList ps -> collect_patterns ps
             | FStar_Parser_AST.PatOr ps -> collect_patterns ps
             | FStar_Parser_AST.PatTuple (ps,uu____5059) ->
                 collect_patterns ps
             | FStar_Parser_AST.PatRecord lidpats ->
                 FStar_List.iter
                   (fun uu____5080  ->
                      match uu____5080 with
                      | (uu____5085,p) -> collect_pattern p) lidpats
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.None )) ->
                 (collect_pattern p; collect_term t)
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           
           and collect_branches bs = FStar_List.iter collect_branch bs
           
           and collect_branch uu____5130 =
             match uu____5130 with
             | (pat,t1,t2) ->
                 (collect_pattern pat;
                  FStar_Util.iter_opt t1 collect_term;
                  collect_term t2)
            in
           let uu____5148 = FStar_Parser_Driver.parse_file filename  in
           match uu____5148 with
           | (ast,uu____5174) ->
               (collect_module ast;
                (let pd1 =
                   let uu____5191 =
                     let uu____5194 = FStar_ST.op_Bang pd  in
                     FStar_List.rev uu____5194  in
                   Mk_pd uu____5191  in
                 let uu____5220 = from_parsing_data pd1 original_map filename
                    in
                 match uu____5220 with
                 | (deps,has_inline_for_extraction,mo_roots) ->
                     (pd1, deps, has_inline_for_extraction, mo_roots))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____5279 = FStar_Util.smap_create Prims.int_zero  in
  FStar_Util.mk_ref uu____5279 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5401 = dep_graph  in
    match uu____5401 with
    | Deps g -> let uu____5405 = FStar_Util.smap_copy g  in Deps uu____5405
  
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
          let uu____5447 = dep_graph  in
          match uu____5447 with
          | Deps dg ->
              let uu____5456 = deps_empty ()  in
              (match uu____5456 with
               | Deps dg' ->
                   let widen_one deps =
                     FStar_All.pipe_right deps
                       (FStar_List.map
                          (fun d  ->
                             match d with
                             | PreferInterface m when
                                 (FStar_List.contains m friends) &&
                                   (has_implementation file_system_map m)
                                 ->
                                 (FStar_ST.op_Colon_Equals widened1 true;
                                  FriendImplementation m)
                             | uu____5511 -> d))
                      in
                   (FStar_Util.smap_fold dg
                      (fun filename  ->
                         fun dep_node  ->
                           fun uu____5519  ->
                             let uu____5521 =
                               let uu___984_5522 = dep_node  in
                               let uu____5523 = widen_one dep_node.edges  in
                               { edges = uu____5523; color = White }  in
                             FStar_Util.smap_add dg' filename uu____5521) ();
                    (let uu____5524 = FStar_ST.op_Bang widened1  in
                     (uu____5524, (Deps dg')))))
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____5690 filename =
              match uu____5690 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____5731 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5731  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5762 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep")
                            in
                         if uu____5762
                         then
                           let uu____5766 =
                             let uu____5768 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____5768  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5766
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1006_5779 = dep_node  in
                           { edges = (uu___1006_5779.edges); color = Gray });
                        (let uu____5780 =
                           let uu____5791 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5791
                            in
                         match uu____5780 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1012_5827 = dep_node  in
                                 {
                                   edges = (uu___1012_5827.edges);
                                   color = Black
                                 });
                              (let uu____5829 =
                                 FStar_Options.debug_at_level_no_module
                                   (FStar_Options.Other "Dep")
                                  in
                               if uu____5829
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5836 =
                                 let uu____5840 =
                                   FStar_List.collect
                                     (fun uu___14_5847  ->
                                        match uu___14_5847 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____5840 all_friends1
                                  in
                               (uu____5836, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            let uu____5912 = all_friend_deps dep_graph [] ([], []) root_files
               in
            match uu____5912 with
            | (friends,all_files_0) ->
                ((let uu____5955 =
                    FStar_Options.debug_at_level_no_module
                      (FStar_Options.Other "Dep")
                     in
                  if uu____5955
                  then
                    let uu____5959 =
                      let uu____5961 =
                        FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                          friends
                         in
                      FStar_String.concat ", " uu____5961  in
                    FStar_Util.print3
                      "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                      (FStar_String.concat ", " all_files_0) uu____5959
                      (FStar_String.concat ", " interfaces_needing_inlining)
                  else ());
                 (let uu____5979 =
                    widen_deps friends dep_graph file_system_map widened  in
                  match uu____5979 with
                  | (widened1,dep_graph1) ->
                      let uu____5997 =
                        (let uu____6009 =
                           FStar_Options.debug_at_level_no_module
                             (FStar_Options.Other "Dep")
                            in
                         if uu____6009
                         then
                           FStar_Util.print_string
                             "==============Phase2==================\n"
                         else ());
                        all_friend_deps dep_graph1 [] ([], []) root_files  in
                      (match uu____5997 with
                       | (uu____6033,all_files) ->
                           ((let uu____6048 =
                               FStar_Options.debug_at_level_no_module
                                 (FStar_Options.Other "Dep")
                                in
                             if uu____6048
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
          (let uu____6095 =
             FStar_Options.debug_at_level_no_module
               (FStar_Options.Other "Dep")
              in
           if uu____6095
           then
             FStar_Util.print_string
               "==============Phase1==================\n"
           else ());
          (let widened = false  in
           let uu____6105 = (FStar_Options.cmi ()) && for_extraction  in
           if uu____6105
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
            let uu____6172 =
              phase1 file_system_map dep_graph interfaces_needing_inlining
                for_extraction
               in
            match uu____6172 with
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
                let uu____6249 = FStar_Options.find_file fn  in
                match uu____6249 with
                | FStar_Pervasives_Native.None  ->
                    let uu____6255 =
                      let uu____6261 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____6261)
                       in
                    FStar_Errors.raise_err uu____6255
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____6291 =
          let uu____6295 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____6295  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6291  in
      let parse_results = FStar_Util.smap_create (Prims.of_int (40))  in
      let rec discover_one file_name =
        let uu____6362 =
          let uu____6364 = deps_try_find dep_graph file_name  in
          uu____6364 = FStar_Pervasives_Native.None  in
        if uu____6362
        then
          let uu____6370 =
            let uu____6386 =
              let uu____6400 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____6400 file_name  in
            match uu____6386 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None  ->
                let uu____6530 =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                (match uu____6530 with
                 | (parsing_data,deps,needs_interface_inlining,additional_roots)
                     ->
                     (parsing_data,
                       (deps, additional_roots, needs_interface_inlining)))
             in
          match uu____6370 with
          | (parsing_data,(deps,mo_roots,needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name parsing_data;
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____6624 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____6624
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____6632 = FStar_List.unique deps1  in
                  { edges = uu____6632; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____6634 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____6634)))
        else ()  in
      profile
        (fun uu____6644  -> FStar_List.iter discover_one all_cmd_line_files1)
        "FStar.Parser.Dep.discover";
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____6677 =
            let uu____6683 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____6683)  in
          FStar_Errors.raise_err uu____6677)
          in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let mo_files = FStar_Util.mk_ref []  in
         let rec aux cycle filename =
           let node =
             let uu____6735 = deps_try_find dep_graph1 filename  in
             match uu____6735 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____6739 =
                   FStar_Util.format1
                     "Impossible: Failed to find dependencies of %s" filename
                    in
                 failwith uu____6739
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____6753 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6753 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6764 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____6770 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6770 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6781 -> [x; UseImplementation f])
                     | uu____6785 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1133_6788 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____6790 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6790);
                deps_add_dep dep_graph1 filename
                  (let uu___1138_6801 = node  in
                   { edges = direct_deps; color = Black });
                (let uu____6802 = is_interface filename  in
                 if uu____6802
                 then
                   let uu____6805 =
                     let uu____6809 = lowercase_module_name filename  in
                     implementation_of_internal file_system_map1 uu____6809
                      in
                   FStar_Util.iter_opt uu____6805
                     (fun impl  ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu____6818 =
                            let uu____6822 = FStar_ST.op_Bang mo_files  in
                            impl :: uu____6822  in
                          FStar_ST.op_Colon_Equals mo_files uu____6818
                        else ())
                 else ()))
            in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu____6884 = FStar_ST.op_Bang mo_files  in
          FStar_List.iter (aux []) uu____6884)
          in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____6956 =
          profile
            (fun uu____6975  ->
               let uu____6976 =
                 let uu____6978 = FStar_Options.codegen ()  in
                 uu____6978 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____6976)
            "FStar.Parser.Dep.topological_dependences_of"
           in
        match uu____6956 with
        | (all_files,uu____6992) ->
            ((let uu____7002 =
                FStar_Options.debug_at_level_no_module
                  (FStar_Options.Other "Dep")
                 in
              if uu____7002
              then
                FStar_Util.print1 "Interfaces needing inlining: %s\n"
                  (FStar_String.concat ", " inlining_ifaces)
              else ());
             (all_files,
               (mk_deps dep_graph file_system_map all_cmd_line_files1
                  all_files inlining_ifaces parse_results)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun deps  ->
    fun f  ->
      dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files
        f
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____7056 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____7082  ->
              match uu____7082 with
              | (m,d) ->
                  let uu____7096 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____7096))
       in
    FStar_All.pipe_right uu____7056 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun deps  ->
    let file_system_map = deps.file_system_map  in
    let all_cmd_line_files = deps.cmd_line_files  in
    let deps1 = deps.dep_graph  in
    let keys = deps_keys deps1  in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun f  ->
            let dep_node =
              let uu____7131 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____7131 FStar_Option.get  in
            let files =
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                dep_node.edges
               in
            let files1 =
              FStar_List.map (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                files
               in
            FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))
  
let (print_raw : deps -> unit) =
  fun deps  ->
    let uu____7160 = deps.dep_graph  in
    match uu____7160 with
    | Deps deps1 ->
        let uu____7164 =
          let uu____7166 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____7184 =
                       let uu____7186 =
                         let uu____7188 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____7188
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7186
                        in
                     uu____7184 :: out) []
             in
          FStar_All.pipe_right uu____7166 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____7164 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules = FStar_Util.smap_create (Prims.of_int (41))
         in
      let should_visit lc_module_name =
        (let uu____7260 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7260) ||
          (let uu____7267 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7267)
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
            let uu____7310 =
              let uu____7314 = FStar_ST.op_Bang order  in ml_file ::
                uu____7314
               in
            FStar_ST.op_Colon_Equals order uu____7310
         in
      let rec aux uu___15_7377 =
        match uu___15_7377 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7405 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7405 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7408 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7408
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7412;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7421 = should_visit lc_module_name  in
              if uu____7421
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7429 = implementation_of deps lc_module_name  in
                  visit_file uu____7429);
                 (let uu____7434 = interface_of deps lc_module_name  in
                  visit_file uu____7434);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7446 = FStar_ST.op_Bang order  in FStar_List.rev uu____7446)
       in
    let sb =
      let uu____7477 = FStar_BigInt.of_int_fs (Prims.of_int (10000))  in
      FStar_StringBuffer.create uu____7477  in
    let pr str =
      let uu____7487 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____7487  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7540 =
          let uu____7542 =
            let uu____7546 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7546  in
          FStar_Option.get uu____7542  in
        FStar_Util.replace_chars uu____7540 46 "_"  in
      let uu____7551 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____7551  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7573 = output_file ".ml" f  in norm_path uu____7573  in
    let output_krml_file f =
      let uu____7585 = output_file ".krml" f  in norm_path uu____7585  in
    let output_cmx_file f =
      let uu____7597 = output_file ".cmx" f  in norm_path uu____7597  in
    let cache_file f =
      let uu____7609 = cache_file_name f  in norm_path uu____7609  in
    let uu____7611 =
      phase1 deps.file_system_map deps.dep_graph
        deps.interfaces_with_inlining true
       in
    match uu____7611 with
    | (widened,dep_graph) ->
        let all_checked_files =
          FStar_All.pipe_right keys
            (FStar_List.fold_left
               (fun all_checked_files  ->
                  fun file_name  ->
                    let process_one_key uu____7653 =
                      let dep_node =
                        let uu____7655 =
                          deps_try_find deps.dep_graph file_name  in
                        FStar_All.pipe_right uu____7655 FStar_Option.get  in
                      let uu____7660 =
                        let uu____7672 = is_interface file_name  in
                        if uu____7672
                        then
                          (FStar_Pervasives_Native.None,
                            FStar_Pervasives_Native.None)
                        else
                          (let uu____7698 =
                             let uu____7702 = lowercase_module_name file_name
                                in
                             interface_of deps uu____7702  in
                           match uu____7698 with
                           | FStar_Pervasives_Native.None  ->
                               (FStar_Pervasives_Native.None,
                                 FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.Some iface ->
                               let uu____7729 =
                                 let uu____7734 =
                                   let uu____7737 =
                                     let uu____7738 =
                                       deps_try_find deps.dep_graph iface  in
                                     FStar_Option.get uu____7738  in
                                   uu____7737.edges  in
                                 FStar_Pervasives_Native.Some uu____7734  in
                               ((FStar_Pervasives_Native.Some iface),
                                 uu____7729))
                         in
                      match uu____7660 with
                      | (iface_fn,iface_deps) ->
                          let iface_deps1 =
                            FStar_Util.map_opt iface_deps
                              (FStar_List.filter
                                 (fun iface_dep  ->
                                    let uu____7782 =
                                      FStar_Util.for_some
                                        (dep_subsumed_by iface_dep)
                                        dep_node.edges
                                       in
                                    Prims.op_Negation uu____7782))
                             in
                          let norm_f = norm_path file_name  in
                          let files =
                            FStar_List.map
                              (file_of_dep_aux true deps.file_system_map
                                 deps.cmd_line_files) dep_node.edges
                             in
                          let files1 =
                            match iface_deps1 with
                            | FStar_Pervasives_Native.None  -> files
                            | FStar_Pervasives_Native.Some iface_deps2 ->
                                let iface_files =
                                  FStar_List.map
                                    (file_of_dep_aux true
                                       deps.file_system_map
                                       deps.cmd_line_files) iface_deps2
                                   in
                                FStar_Util.remove_dups
                                  (fun x  -> fun y  -> x = y)
                                  (FStar_List.append files iface_files)
                             in
                          let files2 =
                            let uu____7825 =
                              FStar_All.pipe_right iface_fn
                                FStar_Util.is_some
                               in
                            if uu____7825
                            then
                              let iface_fn1 =
                                FStar_All.pipe_right iface_fn FStar_Util.must
                                 in
                              let uu____7843 =
                                FStar_All.pipe_right files1
                                  (FStar_List.filter
                                     (fun f  -> f <> iface_fn1))
                                 in
                              FStar_All.pipe_right uu____7843
                                (fun files2  ->
                                   let uu____7870 = cache_file_name iface_fn1
                                      in
                                   uu____7870 :: files2)
                            else files1  in
                          let files3 = FStar_List.map norm_path files2  in
                          let files4 =
                            FStar_List.map
                              (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                              files3
                             in
                          let files5 = FStar_String.concat "\\\n\t" files4
                             in
                          let cache_file_name1 = cache_file file_name  in
                          let all_checked_files1 =
                            let uu____7901 =
                              let uu____7903 =
                                let uu____7905 =
                                  module_name_of_file file_name  in
                                FStar_Options.should_be_already_cached
                                  uu____7905
                                 in
                              Prims.op_Negation uu____7903  in
                            if uu____7901
                            then
                              (print_entry cache_file_name1 norm_f files5;
                               cache_file_name1
                               ::
                               all_checked_files)
                            else all_checked_files  in
                          let uu____7915 =
                            let uu____7924 = FStar_Options.cmi ()  in
                            if uu____7924
                            then
                              profile
                                (fun uu____7945  ->
                                   let uu____7946 = dep_graph_copy dep_graph
                                      in
                                   topological_dependences_of'
                                     deps.file_system_map uu____7946
                                     deps.interfaces_with_inlining
                                     [file_name] widened)
                                "FStar.Parser.Dep.topological_dependences_of_2"
                            else
                              (let maybe_widen_deps f_deps =
                                 FStar_List.map
                                   (fun dep1  ->
                                      file_of_dep_aux false
                                        deps.file_system_map
                                        deps.cmd_line_files dep1) f_deps
                                  in
                               let fst_files =
                                 maybe_widen_deps dep_node.edges  in
                               let fst_files_from_iface =
                                 match iface_deps1 with
                                 | FStar_Pervasives_Native.None  -> []
                                 | FStar_Pervasives_Native.Some iface_deps2
                                     -> maybe_widen_deps iface_deps2
                                  in
                               let uu____7984 =
                                 FStar_Util.remove_dups
                                   (fun x  -> fun y  -> x = y)
                                   (FStar_List.append fst_files
                                      fst_files_from_iface)
                                  in
                               (uu____7984, false))
                             in
                          (match uu____7915 with
                           | (all_fst_files_dep,widened1) ->
                               let all_checked_fst_dep_files =
                                 FStar_All.pipe_right all_fst_files_dep
                                   (FStar_List.map cache_file)
                                  in
                               let all_checked_fst_dep_files_string =
                                 FStar_String.concat " \\\n\t"
                                   all_checked_fst_dep_files
                                  in
                               ((let uu____8031 = is_implementation file_name
                                    in
                                 if uu____8031
                                 then
                                   ((let uu____8035 =
                                       (FStar_Options.cmi ()) && widened1  in
                                     if uu____8035
                                     then
                                       ((let uu____8039 =
                                           output_ml_file file_name  in
                                         print_entry uu____8039
                                           cache_file_name1
                                           all_checked_fst_dep_files_string);
                                        (let uu____8041 =
                                           output_krml_file file_name  in
                                         print_entry uu____8041
                                           cache_file_name1
                                           all_checked_fst_dep_files_string))
                                     else
                                       ((let uu____8046 =
                                           output_ml_file file_name  in
                                         print_entry uu____8046
                                           cache_file_name1 "");
                                        (let uu____8049 =
                                           output_krml_file file_name  in
                                         print_entry uu____8049
                                           cache_file_name1 "")));
                                    (let cmx_files =
                                       let extracted_fst_files =
                                         FStar_All.pipe_right
                                           all_fst_files_dep
                                           (FStar_List.filter
                                              (fun df  ->
                                                 (let uu____8074 =
                                                    lowercase_module_name df
                                                     in
                                                  let uu____8076 =
                                                    lowercase_module_name
                                                      file_name
                                                     in
                                                  uu____8074 <> uu____8076)
                                                   &&
                                                   (let uu____8080 =
                                                      lowercase_module_name
                                                        df
                                                       in
                                                    FStar_Options.should_extract
                                                      uu____8080)))
                                          in
                                       FStar_All.pipe_right
                                         extracted_fst_files
                                         (FStar_List.map output_cmx_file)
                                        in
                                     let uu____8090 =
                                       let uu____8092 =
                                         lowercase_module_name file_name  in
                                       FStar_Options.should_extract
                                         uu____8092
                                        in
                                     if uu____8090
                                     then
                                       let cmx_files1 =
                                         FStar_String.concat "\\\n\t"
                                           cmx_files
                                          in
                                       let uu____8098 =
                                         output_cmx_file file_name  in
                                       let uu____8100 =
                                         output_ml_file file_name  in
                                       print_entry uu____8098 uu____8100
                                         cmx_files1
                                     else ()))
                                 else
                                   (let uu____8106 =
                                      (let uu____8110 =
                                         let uu____8112 =
                                           lowercase_module_name file_name
                                            in
                                         has_implementation
                                           deps.file_system_map uu____8112
                                          in
                                       Prims.op_Negation uu____8110) &&
                                        (is_interface file_name)
                                       in
                                    if uu____8106
                                    then
                                      let uu____8115 =
                                        (FStar_Options.cmi ()) &&
                                          (widened1 || true)
                                         in
                                      (if uu____8115
                                       then
                                         let uu____8119 =
                                           output_krml_file file_name  in
                                         print_entry uu____8119
                                           cache_file_name1
                                           all_checked_fst_dep_files_string
                                       else
                                         (let uu____8123 =
                                            output_krml_file file_name  in
                                          print_entry uu____8123
                                            cache_file_name1 ""))
                                    else ()));
                                all_checked_files1))
                       in
                    profile process_one_key
                      "FStar.Parser.Dep.process_one_key") [])
           in
        let all_fst_files =
          let uu____8137 =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation)
             in
          FStar_All.pipe_right uu____8137
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_fsti_files =
          let uu____8159 =
            FStar_All.pipe_right keys (FStar_List.filter is_interface)  in
          FStar_All.pipe_right uu____8159
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.of_int (41))  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8200 = FStar_Options.should_extract mname  in
                  if uu____8200
                  then
                    let uu____8203 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____8203
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.of_int (41))  in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8230 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____8230));
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
  fun deps  ->
    let uu____8280 = FStar_Options.dep ()  in
    match uu____8280 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        profile (fun uu____8289  -> print_full deps)
          "FStar.Parser.Deps.print_full_deps"
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8295 ->
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
         fun uu____8350  ->
           fun s  ->
             match uu____8350 with
             | (v0,v1) ->
                 let uu____8379 =
                   let uu____8381 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____8381  in
                 FStar_String.op_Hat s uu____8379) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8402 =
        let uu____8404 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8404  in
      has_interface deps.file_system_map uu____8402
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8420 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8420  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8431 =
                   let uu____8433 = module_name_of_file f  in
                   FStar_String.lowercase uu____8433  in
                 uu____8431 = m)))
  