open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____20 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____31 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____42 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____65 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____76 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____87 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____98 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____109 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____157 =
             (l > lext) &&
               (let uu____160 = FStar_String.substring f (l - lext) lext  in
                uu____160 = ext)
              in
           if uu____157
           then
             let uu____167 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____167
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____174 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____174 with
    | (FStar_Pervasives_Native.Some m)::uu____188 ->
        FStar_Pervasives_Native.Some m
    | uu____200 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____217 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____217 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____231 = is_interface f  in Prims.op_Negation uu____231 
let list_of_option :
  'Auu____238 .
    'Auu____238 FStar_Pervasives_Native.option -> 'Auu____238 Prims.list
  =
  fun uu___0_247  ->
    match uu___0_247 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____256 .
    ('Auu____256 FStar_Pervasives_Native.option * 'Auu____256
      FStar_Pervasives_Native.option) -> 'Auu____256 Prims.list
  =
  fun uu____271  ->
    match uu____271 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____299 =
      let uu____303 = FStar_Util.basename f  in
      check_and_strip_suffix uu____303  in
    match uu____299 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____310 =
          let uu____316 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____316)  in
        FStar_Errors.raise_err uu____310
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____330 = module_name_of_file f  in
    FStar_String.lowercase uu____330
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____355 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____355 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____368 ->
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
    match projectee with | UseInterface _0 -> true | uu____425 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____448 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____471 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____494 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_512  ->
    match uu___1_512 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____531 . unit -> 'Auu____531 Prims.list =
  fun uu____534  -> [] 
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
type parsing_data =
  {
  direct_deps: dependence Prims.list ;
  additional_roots: dependence Prims.list ;
  has_inline_for_extraction: Prims.bool }
let (__proj__Mkparsing_data__item__direct_deps :
  parsing_data -> dependence Prims.list) =
  fun projectee  ->
    match projectee with
    | { direct_deps; additional_roots; has_inline_for_extraction;_} ->
        direct_deps
  
let (__proj__Mkparsing_data__item__additional_roots :
  parsing_data -> dependence Prims.list) =
  fun projectee  ->
    match projectee with
    | { direct_deps; additional_roots; has_inline_for_extraction;_} ->
        additional_roots
  
let (__proj__Mkparsing_data__item__has_inline_for_extraction :
  parsing_data -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { direct_deps; additional_roots; has_inline_for_extraction;_} ->
        has_inline_for_extraction
  
let (empty_parsing_data : parsing_data) =
  {
    direct_deps = [];
    additional_roots = [];
    has_inline_for_extraction = false
  } 
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
  fun uu____1084  ->
    fun k  -> match uu____1084 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____1116  ->
    fun k  ->
      fun v1  -> match uu____1116 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____1139  -> match uu____1139 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____1157  ->
    let uu____1158 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____1158
  
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
  let uu____1263 = deps_empty ()  in
  let uu____1266 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____1278 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____1263 uu____1266 [] [] [] uu____1278 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___2_1297  ->
    match uu___2_1297 with
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
      let uu____1326 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1326 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1353) ->
          let uu____1375 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1375
      | FStar_Pervasives_Native.Some
          (uu____1378,FStar_Pervasives_Native.Some fn) ->
          let uu____1401 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1401
      | uu____1404 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1437 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1437 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1464) ->
          FStar_Pervasives_Native.Some iface
      | uu____1487 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1520 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1520 with
      | FStar_Pervasives_Native.Some
          (uu____1546,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1570 -> FStar_Pervasives_Native.None
  
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
      let uu____1659 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1659
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1679 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1679
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1714 =
      let uu____1718 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1718  in
    match uu____1714 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1729 =
            ((let uu____1733 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1733) &&
               (let uu____1739 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1739))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1742 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1742))
             in
          if uu____1729
          then
            let uu____1745 =
              let uu____1751 =
                let uu____1753 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1753
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1751)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1745
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1760 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1760
        then
          let uu____1766 =
            let uu____1772 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1772)
             in
          FStar_Errors.raise_err uu____1766
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____1808 = FStar_Util.smap_try_find memo x  in
    match uu____1808 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1852 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1852 FStar_Util.must
  
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
                      (let uu____1921 = lowercase_module_name fn  in
                       key = uu____1921)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1940 = interface_of_internal file_system_map key  in
              (match uu____1940 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1947 =
                     let uu____1953 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1953)  in
                   FStar_Errors.raise_err uu____1947
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1963 =
                (cmd_line_has_impl key) &&
                  (let uu____1966 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1966)
                 in
              if uu____1963
              then
                let uu____1973 = FStar_Options.expose_interfaces ()  in
                (if uu____1973
                 then
                   let uu____1977 =
                     let uu____1979 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____1979  in
                   maybe_use_cache_of uu____1977
                 else
                   (let uu____1986 =
                      let uu____1992 =
                        let uu____1994 =
                          let uu____1996 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____1996  in
                        let uu____2001 =
                          let uu____2003 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____2003  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1994 uu____2001
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1992)
                       in
                    FStar_Errors.raise_err uu____1986))
              else
                (let uu____2013 =
                   let uu____2015 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____2015  in
                 maybe_use_cache_of uu____2013)
          | PreferInterface key ->
              let uu____2022 = implementation_of_internal file_system_map key
                 in
              (match uu____2022 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2028 =
                     let uu____2034 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2034)
                      in
                   FStar_Errors.raise_err uu____2028
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____2044 = implementation_of_internal file_system_map key
                 in
              (match uu____2044 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2050 =
                     let uu____2056 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2056)
                      in
                   FStar_Errors.raise_err uu____2050
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____2066 = implementation_of_internal file_system_map key
                 in
              (match uu____2066 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2072 =
                     let uu____2078 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2078)
                      in
                   FStar_Errors.raise_err uu____2072
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
          let uu____2141 = deps_try_find deps fn  in
          match uu____2141 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____2153;_} ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____2171 =
       let uu____2173 =
         let uu____2175 =
           let uu____2177 =
             let uu____2181 =
               let uu____2185 = deps_keys graph  in
               FStar_List.unique uu____2185  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____2199 =
                      let uu____2204 = deps_try_find graph k  in
                      FStar_Util.must uu____2204  in
                    uu____2199.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____2229 =
                      let uu____2231 = lowercase_module_name k  in
                      r uu____2231  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2229
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____2181
              in
           FStar_String.concat "\n" uu____2177  in
         FStar_String.op_Hat uu____2175 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____2173  in
     FStar_Util.write_file "dep.graph" uu____2171)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____2252  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____2278 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____2278  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____2318 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____2318
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____2355 =
              let uu____2361 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____2361)  in
            FStar_Errors.raise_err uu____2355)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____2424 = FStar_Util.smap_try_find map1 key  in
      match uu____2424 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2471 = is_interface full_path  in
          if uu____2471
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2520 = is_interface full_path  in
          if uu____2520
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2562 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2580  ->
          match uu____2580 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2562);
    FStar_List.iter
      (fun f  ->
         let uu____2599 = lowercase_module_name f  in add_entry uu____2599 f)
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
        (let uu____2631 =
           let uu____2635 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2635  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2671 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2671  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2631);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2799 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2799 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2834 = string_of_lid l last1  in
      FStar_String.lowercase uu____2834
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2851 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2851
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2883 =
        let uu____2885 =
          let uu____2887 =
            let uu____2889 =
              let uu____2893 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2893  in
            FStar_Util.must uu____2889  in
          FStar_String.lowercase uu____2887  in
        uu____2885 <> k'  in
      if uu____2883
      then
        let uu____2898 = FStar_Ident.range_of_lid lid  in
        let uu____2899 =
          let uu____2905 =
            let uu____2907 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2907 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2905)  in
        FStar_Errors.log_issue uu____2898 uu____2899
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2923 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2949 = FStar_Options.prims_basename ()  in
      let uu____2951 =
        let uu____2955 = FStar_Options.pervasives_basename ()  in
        let uu____2957 =
          let uu____2961 = FStar_Options.pervasives_native_basename ()  in
          [uu____2961]  in
        uu____2955 :: uu____2957  in
      uu____2949 :: uu____2951  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____3044 =
         let uu____3051 = lowercase_module_name full_filename  in
         namespace_of_module uu____3051  in
       match uu____3044 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____3122 -> d = d'
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        parsing_data)
  =
  fun original_map  ->
    fun filename  ->
      fun get_parsing_data_from_cache  ->
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____3180 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____3180
        then
          ((let uu____3196 = FStar_Options.debug_any ()  in
            if uu____3196
            then
              FStar_Util.print1
                "Reading parsing data for %s from its checked file\n"
                filename
            else ());
           FStar_All.pipe_right data_from_cache FStar_Util.must)
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____3240 =
             let uu____3241 = is_interface filename  in
             if uu____3241
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____3363 =
               let uu____3365 =
                 let uu____3367 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____3367  in
               Prims.op_Negation uu____3365  in
             if uu____3363
             then
               let uu____3394 =
                 let uu____3397 = FStar_ST.op_Bang deps1  in d :: uu____3397
                  in
               FStar_ST.op_Colon_Equals deps1 uu____3394
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____3502 = resolve_module_name original_or_working_map key
                in
             match uu____3502 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____3512 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____3512
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____3518 -> false  in
           let record_open_module let_open lid =
             let uu____3545 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____3545
             then true
             else
               (if let_open
                then
                  (let uu____3554 = FStar_Ident.range_of_lid lid  in
                   let uu____3555 =
                     let uu____3561 =
                       let uu____3563 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____3563
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3561)
                      in
                   FStar_Errors.log_issue uu____3554 uu____3555)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____3591 = FStar_Ident.range_of_lid lid  in
               let uu____3592 =
                 let uu____3598 =
                   let uu____3600 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____3600
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____3598)
                  in
               FStar_Errors.log_issue uu____3591 uu____3592
             else ()  in
           let record_open let_open lid =
             let uu____3628 = record_open_module let_open lid  in
             if uu____3628
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____3649 =
             match uu____3649 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____3668 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____3697 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____3697  in
             let alias = lowercase_join_longident lid true  in
             let uu____3702 = FStar_Util.smap_try_find original_map alias  in
             match uu____3702 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3770 = FStar_Ident.range_of_lid lid  in
                   let uu____3771 =
                     let uu____3777 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3777)
                      in
                   FStar_Errors.log_issue uu____3770 uu____3771);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____3796 = add_dependence_edge working_map module_name  in
             if uu____3796
             then ()
             else
               (let uu____3801 = FStar_Options.debug_any ()  in
                if uu____3801
                then
                  let uu____3804 = FStar_Ident.range_of_lid module_name  in
                  let uu____3805 =
                    let uu____3811 =
                      let uu____3813 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____3813
                       in
                    (FStar_Errors.Warning_UnboundModuleReference, uu____3811)
                     in
                  FStar_Errors.log_issue uu____3804 uu____3805
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____3835 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___3_4017 =
              match uu___3_4017 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____4048 =
                        let uu____4050 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____4050
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____4056) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____4087 =
                        let uu____4089 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____4089
                         in
                      ())
                   else ();
                   collect_decls decls)
            
            and collect_decls decls =
              FStar_List.iter
                (fun x  ->
                   collect_decl x.FStar_Parser_AST.d;
                   FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                   if
                     FStar_List.contains
                       FStar_Parser_AST.Inline_for_extraction
                       x.FStar_Parser_AST.quals
                   then set_interface_inlining ()
                   else ()) decls
            
            and collect_decl d =
              match d with
              | FStar_Parser_AST.Include lid -> record_open false lid
              | FStar_Parser_AST.Open lid -> record_open false lid
              | FStar_Parser_AST.Friend lid ->
                  let uu____4141 =
                    let uu____4142 = lowercase_join_longident lid true  in
                    FriendImplementation uu____4142  in
                  add_dep deps uu____4141
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____4159 = record_module_alias ident lid  in
                  if uu____4159
                  then
                    let uu____4162 =
                      let uu____4163 = lowercase_join_longident lid true  in
                      dep_edge uu____4163  in
                    add_dep deps uu____4162
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____4168,patterms) ->
                  FStar_List.iter
                    (fun uu____4205  ->
                       match uu____4205 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____4232,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____4248,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____4260;
                    FStar_Parser_AST.mdest = uu____4261;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____4274;
                    FStar_Parser_AST.mdest = uu____4275;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____4288,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____4300;
                    FStar_Parser_AST.mdest = uu____4301;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____4325,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____4364  ->
                           match uu____4364 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____4377,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____4397 -> ()
              | FStar_Parser_AST.Pragma uu____4398 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____4405 =
                      let uu____4407 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____4407 > (Prims.parse_int "1")  in
                    if uu____4405
                    then
                      let uu____4432 =
                        let uu____4438 =
                          let uu____4440 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____4440
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____4438)  in
                      let uu____4445 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____4432 uu____4445
                    else ()))
            
            and collect_tycon uu___4_4448 =
              match uu___4_4448 with
              | FStar_Parser_AST.TyconAbstract (uu____4449,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____4482,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____4523,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____4605  ->
                        match uu____4605 with
                        | (uu____4619,t,uu____4621) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____4636,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____4734  ->
                        match uu____4734 with
                        | (uu____4753,t,uu____4755,uu____4756) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___5_4780 =
              match uu___5_4780 with
              | FStar_Parser_AST.DefineEffect (uu____4781,binders,t,decls) ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____4823,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____4866,t);
                   FStar_Parser_AST.brange = uu____4868;
                   FStar_Parser_AST.blevel = uu____4869;
                   FStar_Parser_AST.aqual = uu____4870;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____4883,t);
                   FStar_Parser_AST.brange = uu____4885;
                   FStar_Parser_AST.blevel = uu____4886;
                   FStar_Parser_AST.aqual = uu____4887;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____4901;
                   FStar_Parser_AST.blevel = uu____4902;
                   FStar_Parser_AST.aqual = uu____4903;_} -> collect_term t
               | uu____4909 -> ())
            
            and collect_aqual uu___6_4914 =
              match uu___6_4914 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____4921 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___7_4928 =
              match uu___7_4928 with
              | FStar_Const.Const_int
                  (uu____4929,FStar_Pervasives_Native.Some
                   (signedness,width))
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
                  let uu____4956 =
                    let uu____4957 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____4957  in
                  add_dep deps uu____4956
              | FStar_Const.Const_char uu____4960 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____4963 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____4965 -> ()
            
            and collect_term' uu___10_4966 =
              match uu___10_4966 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____4985 =
                      let uu____4987 = FStar_Ident.text_of_id s  in
                      uu____4987 = "@"  in
                    if uu____4985
                    then
                      let uu____4992 =
                        let uu____4993 =
                          let uu____5002 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____5002
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____4993  in
                      collect_term' uu____4992
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____5009 -> ()
              | FStar_Parser_AST.Uvar uu____5012 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____5021) -> record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____5083  ->
                        match uu____5083 with
                        | (t,uu____5092) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____5118) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____5132,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____5212  ->
                        match uu____5212 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____5270 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____5300,t1,t2) ->
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
                     (fun uu____5555  ->
                        match uu____5555 with
                        | (uu____5567,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____5584) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___8_5668  ->
                        match uu___8_5668 with
                        | FStar_Util.Inl b -> collect_binder b
                        | FStar_Util.Inr t1 -> collect_term t1) binders;
                   collect_term t)
              | FStar_Parser_AST.QForall (binders,(uu____5704,ts),t) ->
                  (collect_binders binders;
                   FStar_List.iter (FStar_List.iter collect_term) ts;
                   collect_term t)
              | FStar_Parser_AST.QExists (binders,(uu____5773,ts),t) ->
                  (collect_binders binders;
                   FStar_List.iter (FStar_List.iter collect_term) ts;
                   collect_term t)
              | FStar_Parser_AST.Refine (binder,t) ->
                  (collect_binder binder; collect_term t)
              | FStar_Parser_AST.NamedTyp (uu____5858,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____5875) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____5889) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____5903,uu____5904) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____5916) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____5962 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____5962);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___9_5981  ->
                        match uu___9_5981 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___11_6016 =
              match uu___11_6016 with
              | FStar_Parser_AST.PatVar (uu____6017,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____6027,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____6040 -> ()
              | FStar_Parser_AST.PatConst uu____6043 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____6059 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____6075) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____6112  ->
                       match uu____6112 with
                       | (uu____6123,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____6243 =
              match uu____6243 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____6288 = FStar_Parser_Driver.parse_file filename  in
            match uu____6288 with
            | (ast,uu____6304) ->
                let mname = lowercase_module_name filename  in
                ((let uu____6322 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____6322
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____6328 = FStar_ST.op_Bang deps  in
                  let uu____6354 = FStar_ST.op_Bang mo_roots  in
                  let uu____6380 = FStar_ST.op_Bang has_inline_for_extraction
                     in
                  {
                    direct_deps = uu____6328;
                    additional_roots = uu____6354;
                    has_inline_for_extraction = uu____6380
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____6419 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____6419 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____6544 = dep_graph  in
    match uu____6544 with
    | Deps g -> let uu____6553 = FStar_Util.smap_copy g  in Deps uu____6553
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____6706 filename =
              match uu____6706 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____6752 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____6752  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____6787 = FStar_Options.debug_any ()  in
                         if uu____6787
                         then
                           let uu____6790 =
                             let uu____6792 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____6792  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____6790
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___846_6803 = dep_node  in
                           { edges = (uu___846_6803.edges); color = Gray });
                        (let uu____6808 =
                           let uu____6819 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____6819
                            in
                         match uu____6808 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___852_6855 = dep_node  in
                                 {
                                   edges = (uu___852_6855.edges);
                                   color = Black
                                 });
                              (let uu____6861 = FStar_Options.debug_any ()
                                  in
                               if uu____6861
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____6867 =
                                 let uu____6871 =
                                   FStar_List.collect
                                     (fun uu___12_6878  ->
                                        match uu___12_6878 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____6871 all_friends1
                                  in
                               (uu____6867, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____6945 = FStar_Options.debug_any ()  in
             if uu____6945
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____6977 = deps  in
               match uu____6977 with
               | Deps dg ->
                   let uu____6986 = deps_empty ()  in
                   (match uu____6986 with
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
                                      (FStar_ST.op_Colon_Equals widened true;
                                       FriendImplementation m)
                                  | uu____7041 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____7051  ->
                                  let uu____7055 =
                                    let uu___887_7060 = dep_node  in
                                    let uu____7065 = widen_one dep_node.edges
                                       in
                                    { edges = uu____7065; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____7055)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____7071 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____7071
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____7077 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____7077 with
             | (friends,all_files_0) ->
                 ((let uu____7120 = FStar_Options.debug_any ()  in
                   if uu____7120
                   then
                     let uu____7123 =
                       let uu____7125 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____7125  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____7123
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____7146 =
                     (let uu____7158 = FStar_Options.debug_any ()  in
                      if uu____7158
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____7146 with
                   | (uu____7181,all_files) ->
                       ((let uu____7196 = FStar_Options.debug_any ()  in
                         if uu____7196
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____7203 = FStar_ST.op_Bang widened  in
                         (all_files, uu____7203))))))
  
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
                let uu____7309 = FStar_Options.find_file fn  in
                match uu____7309 with
                | FStar_Pervasives_Native.None  ->
                    let uu____7315 =
                      let uu____7321 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____7321)
                       in
                    FStar_Errors.raise_err uu____7315
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____7353 =
          let uu____7357 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____7357  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____7353  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____7430 =
          let uu____7432 = deps_try_find dep_graph file_name  in
          uu____7432 = FStar_Pervasives_Native.None  in
        if uu____7430
        then
          let uu____7444 =
            let uu____7456 =
              let uu____7470 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____7470 file_name  in
            match uu____7456 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____7444 with
          | (deps,mo_roots,needs_interface_inlining) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name
                 {
                   direct_deps = deps;
                   additional_roots = mo_roots;
                   has_inline_for_extraction = needs_interface_inlining
                 };
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____7623 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____7623
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____7635 = FStar_List.unique deps1  in
                  { edges = uu____7635; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____7637 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____7637)))
        else ()  in
      FStar_Options.profile
        (fun uu____7647  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____7650  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____7684 =
            let uu____7690 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____7690)  in
          FStar_Errors.raise_err uu____7684)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____7733 = deps_try_find dep_graph1 filename  in
             match uu____7733 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____7747 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____7747
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____7763 =
                           implementation_of_internal file_system_map f  in
                         (match uu____7763 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____7774 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____7780 =
                           implementation_of_internal file_system_map f  in
                         (match uu____7780 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____7791 -> [x; UseImplementation f])
                     | uu____7795 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___973_7798 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____7804 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____7804);
                deps_add_dep dep_graph1 filename
                  (let uu___978_7814 = node  in
                   { edges = direct_deps; color = Black }))
            in
         FStar_List.iter (aux []) all_command_line_files  in
       full_cycle_detection all_cmd_line_files1;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____7862 =
          FStar_Options.profile
            (fun uu____7881  ->
               let uu____7882 =
                 let uu____7884 = FStar_Options.codegen ()  in
                 uu____7884 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____7882)
            (fun uu____7890  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____7862 with
        | (all_files,uu____7915) ->
            ((let uu____7925 = FStar_Options.debug_any ()  in
              if uu____7925
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
    let uu____7999 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____8025  ->
              match uu____8025 with
              | (m,d) ->
                  let uu____8039 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____8039))
       in
    FStar_All.pipe_right uu____7999 (FStar_String.concat "\n")
  
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
              let uu____8094 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____8094 FStar_Option.get  in
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
    let uu____8145 = deps.dep_graph  in
    match uu____8145 with
    | Deps deps1 ->
        let uu____8153 =
          let uu____8155 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____8177 =
                       let uu____8179 =
                         let uu____8181 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____8181
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____8179
                        in
                     uu____8177 :: out) []
             in
          FStar_All.pipe_right uu____8155 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____8153 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____8267 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____8267) ||
          (let uu____8274 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____8274)
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
            let uu____8317 =
              let uu____8321 = FStar_ST.op_Bang order  in ml_file ::
                uu____8321
               in
            FStar_ST.op_Colon_Equals order uu____8317
         in
      let rec aux uu___13_8384 =
        match uu___13_8384 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____8412 = deps_try_find deps.dep_graph file_name  in
                  (match uu____8412 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8419 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____8419
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____8423;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____8434 = should_visit lc_module_name  in
              if uu____8434
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____8442 = implementation_of deps lc_module_name  in
                  visit_file uu____8442);
                 (let uu____8447 = interface_of deps lc_module_name  in
                  visit_file uu____8447);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____8459 = FStar_ST.op_Bang order  in FStar_List.rev uu____8459)
       in
    let sb =
      let uu____8490 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____8490  in
    let pr str =
      let uu____8500 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____8500  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____8553 =
          let uu____8555 =
            let uu____8559 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____8559  in
          FStar_Option.get uu____8555  in
        FStar_Util.replace_chars uu____8553 46 "_"  in
      let uu____8564 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____8564  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____8586 = output_file ".ml" f  in norm_path uu____8586  in
    let output_krml_file f =
      let uu____8598 = output_file ".krml" f  in norm_path uu____8598  in
    let output_cmx_file f =
      let uu____8610 = output_file ".cmx" f  in norm_path uu____8610  in
    let cache_file f =
      let uu____8622 = cache_file_name f  in norm_path uu____8622  in
    let all_checked_files =
      FStar_All.pipe_right keys
        (FStar_List.fold_left
           (fun all_checked_files  ->
              fun file_name  ->
                let process_one_key uu____8655 =
                  let dep_node =
                    let uu____8661 = deps_try_find deps.dep_graph file_name
                       in
                    FStar_All.pipe_right uu____8661 FStar_Option.get  in
                  let iface_deps =
                    let uu____8679 = is_interface file_name  in
                    if uu____8679
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____8690 =
                         let uu____8694 = lowercase_module_name file_name  in
                         interface_of deps uu____8694  in
                       match uu____8690 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some iface ->
                           let uu____8706 =
                             let uu____8709 =
                               let uu____8714 =
                                 deps_try_find deps.dep_graph iface  in
                               FStar_Option.get uu____8714  in
                             uu____8709.edges  in
                           FStar_Pervasives_Native.Some uu____8706)
                     in
                  let iface_deps1 =
                    FStar_Util.map_opt iface_deps
                      (FStar_List.filter
                         (fun iface_dep  ->
                            let uu____8735 =
                              FStar_Util.for_some (dep_subsumed_by iface_dep)
                                dep_node.edges
                               in
                            Prims.op_Negation uu____8735))
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
                            (file_of_dep_aux true deps.file_system_map
                               deps.cmd_line_files) iface_deps2
                           in
                        FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                          (FStar_List.append files iface_files)
                     in
                  let files2 = FStar_List.map norm_path files1  in
                  let files3 =
                    FStar_List.map
                      (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files2
                     in
                  let files4 =
                    FStar_Options.profile
                      (fun uu____8795  -> FStar_String.concat "\\\n\t" files3)
                      (fun uu____8798  -> "Dependence analysis: concat files")
                     in
                  let cache_file_name1 = cache_file file_name  in
                  let all_checked_files1 =
                    let uu____8807 =
                      let uu____8809 =
                        let uu____8811 = module_name_of_file file_name  in
                        FStar_Options.should_be_already_cached uu____8811  in
                      Prims.op_Negation uu____8809  in
                    if uu____8807
                    then
                      (print_entry cache_file_name1 norm_f files4;
                       cache_file_name1
                       ::
                       all_checked_files)
                    else all_checked_files  in
                  let uu____8821 =
                    let uu____8830 = FStar_Options.cmi ()  in
                    if uu____8830
                    then
                      FStar_Options.profile
                        (fun uu____8850  ->
                           topological_dependences_of deps.file_system_map
                             deps.dep_graph deps.interfaces_with_inlining
                             [file_name] true)
                        (fun uu____8855  ->
                           "Dependence analysis: cmi, second topological sort")
                    else
                      (let maybe_widen_deps f_deps =
                         FStar_List.map
                           (fun dep1  ->
                              file_of_dep_aux false deps.file_system_map
                                deps.cmd_line_files dep1) f_deps
                          in
                       let fst_files = maybe_widen_deps dep_node.edges  in
                       let fst_files_from_iface =
                         match iface_deps1 with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some iface_deps2 ->
                             maybe_widen_deps iface_deps2
                          in
                       let uu____8899 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           (FStar_List.append fst_files fst_files_from_iface)
                          in
                       (uu____8899, false))
                     in
                  match uu____8821 with
                  | (all_fst_files_dep,widened) ->
                      let all_checked_fst_dep_files =
                        FStar_All.pipe_right all_fst_files_dep
                          (FStar_List.map cache_file)
                         in
                      let all_checked_fst_dep_files_string =
                        FStar_String.concat " \\\n\t"
                          all_checked_fst_dep_files
                         in
                      ((let uu____8946 = is_implementation file_name  in
                        if uu____8946
                        then
                          ((let uu____8950 =
                              (FStar_Options.cmi ()) && widened  in
                            if uu____8950
                            then
                              ((let uu____8954 = output_ml_file file_name  in
                                print_entry uu____8954 cache_file_name1
                                  all_checked_fst_dep_files_string);
                               (let uu____8956 = output_krml_file file_name
                                   in
                                print_entry uu____8956 cache_file_name1
                                  all_checked_fst_dep_files_string))
                            else
                              ((let uu____8961 = output_ml_file file_name  in
                                print_entry uu____8961 cache_file_name1 "");
                               (let uu____8964 = output_krml_file file_name
                                   in
                                print_entry uu____8964 cache_file_name1 "")));
                           (let cmx_files =
                              let extracted_fst_files =
                                FStar_All.pipe_right all_fst_files_dep
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____8989 =
                                           lowercase_module_name df  in
                                         let uu____8991 =
                                           lowercase_module_name file_name
                                            in
                                         uu____8989 <> uu____8991) &&
                                          (let uu____8995 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____8995)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            let uu____9005 =
                              let uu____9007 =
                                lowercase_module_name file_name  in
                              FStar_Options.should_extract uu____9007  in
                            if uu____9005
                            then
                              let cmx_files1 =
                                FStar_String.concat "\\\n\t" cmx_files  in
                              let uu____9013 = output_cmx_file file_name  in
                              let uu____9015 = output_ml_file file_name  in
                              print_entry uu____9013 uu____9015 cmx_files1
                            else ()))
                        else
                          (let uu____9021 =
                             (let uu____9025 =
                                let uu____9027 =
                                  lowercase_module_name file_name  in
                                has_implementation deps.file_system_map
                                  uu____9027
                                 in
                              Prims.op_Negation uu____9025) &&
                               (is_interface file_name)
                              in
                           if uu____9021
                           then
                             let uu____9030 =
                               (FStar_Options.cmi ()) && (widened || true)
                                in
                             (if uu____9030
                              then
                                let uu____9034 = output_krml_file file_name
                                   in
                                print_entry uu____9034 cache_file_name1
                                  all_checked_fst_dep_files_string
                              else
                                (let uu____9038 = output_krml_file file_name
                                    in
                                 print_entry uu____9038 cache_file_name1 ""))
                           else ()));
                       all_checked_files1)
                   in
                FStar_Options.profile process_one_key
                  (fun uu____9047  ->
                     FStar_Util.format1 "Dependence analysis: output key %s"
                       file_name)) [])
       in
    let all_fst_files =
      let uu____9057 =
        FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
      FStar_All.pipe_right uu____9057
        (FStar_Util.sort_with FStar_String.compare)
       in
    let all_ml_files =
      let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right all_fst_files
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____9098 = FStar_Options.should_extract mname  in
              if uu____9098
              then
                let uu____9101 = output_ml_file fst_file  in
                FStar_Util.smap_add ml_file_map mname uu____9101
              else ()));
      sort_output_files ml_file_map  in
    let all_krml_files =
      let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____9128 = output_krml_file fst_file  in
              FStar_Util.smap_add krml_file_map mname uu____9128));
      sort_output_files krml_file_map  in
    let print_all tag files =
      pr tag;
      pr "=\\\n\t";
      FStar_List.iter (fun f  -> pr (norm_path f); pr " \\\n\t") files;
      pr "\n"  in
    print_all "ALL_FST_FILES" all_fst_files;
    print_all "ALL_CHECKED_FILES" all_checked_files;
    print_all "ALL_ML_FILES" all_ml_files;
    print_all "ALL_KRML_FILES" all_krml_files;
    FStar_StringBuffer.output_channel FStar_Util.stdout sb
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____9190 = FStar_Options.dep ()  in
    match uu____9190 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____9199  -> print_full deps)
          (fun uu____9201  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____9207 ->
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
         fun uu____9262  ->
           fun s  ->
             match uu____9262 with
             | (v0,v1) ->
                 let uu____9291 =
                   let uu____9293 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____9293  in
                 FStar_String.op_Hat s uu____9291) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____9336 =
        let uu____9338 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____9338  in
      has_interface deps.file_system_map uu____9336
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____9376 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____9376  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____9387 =
                   let uu____9389 = module_name_of_file f  in
                   FStar_String.lowercase uu____9389  in
                 uu____9387 = m)))
  