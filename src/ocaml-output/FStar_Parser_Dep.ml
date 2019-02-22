open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____9 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____20 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____31 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____54 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____65 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____76 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____87 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____98 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____146 =
             (l > lext) &&
               (let uu____159 = FStar_String.substring f (l - lext) lext  in
                uu____159 = ext)
              in
           if uu____146
           then
             let uu____180 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____180
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____197 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____197 with
    | (FStar_Pervasives_Native.Some m)::uu____211 ->
        FStar_Pervasives_Native.Some m
    | uu____223 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____240 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____240 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____254 = is_interface f  in Prims.op_Negation uu____254 
let list_of_option :
  'Auu____261 .
    'Auu____261 FStar_Pervasives_Native.option -> 'Auu____261 Prims.list
  =
  fun uu___11_270  ->
    match uu___11_270 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____279 .
    ('Auu____279 FStar_Pervasives_Native.option * 'Auu____279
      FStar_Pervasives_Native.option) -> 'Auu____279 Prims.list
  =
  fun uu____294  ->
    match uu____294 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____322 =
      let uu____326 = FStar_Util.basename f  in
      check_and_strip_suffix uu____326  in
    match uu____322 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____333 =
          let uu____339 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____339)  in
        FStar_Errors.raise_err uu____333
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____353 = module_name_of_file f  in
    FStar_String.lowercase uu____353
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____366 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____366 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____369 ->
        let uu____372 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____372
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____414 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____438 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____462 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____486 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___12_505  ->
    match uu___12_505 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____524 . unit -> 'Auu____524 Prims.list =
  fun uu____527  -> [] 
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
  fun uu____869  ->
    fun k  -> match uu____869 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____891  ->
    fun k  ->
      fun v1  -> match uu____891 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____906  -> match uu____906 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____918  ->
    let uu____919 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____919
  
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
  let uu____977 = deps_empty ()  in
  let uu____978 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____990 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____977 uu____978 [] [] [] uu____990 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___13_1003  ->
    match uu___13_1003 with
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
      let uu____1032 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1032 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1059) ->
          let uu____1081 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1081
      | FStar_Pervasives_Native.Some
          (uu____1084,FStar_Pervasives_Native.Some fn) ->
          let uu____1107 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1107
      | uu____1110 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1143 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1143 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1170) ->
          FStar_Pervasives_Native.Some iface
      | uu____1193 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1226 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1226 with
      | FStar_Pervasives_Native.Some
          (uu____1252,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1276 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1305 = interface_of file_system_map key  in
      FStar_Option.isSome uu____1305
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1325 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____1325
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____1352 =
        let uu____1354 = FStar_Options.lax ()  in
        if uu____1354 then ".checked.lax" else ".checked"  in
      FStar_String.op_Hat fn uu____1352  in
    let uu____1362 =
      let uu____1366 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1366  in
    match uu____1362 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____1387 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1387
        then
          let uu____1398 =
            let uu____1404 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1404)
             in
          FStar_Errors.raise_err uu____1398
        else
          (let uu____1416 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____1416, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____1430 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____1430 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1466 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1466 FStar_Util.must
  
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
                      (let uu____1520 = lowercase_module_name fn  in
                       key = uu____1520)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1539 = interface_of file_system_map key  in
              (match uu____1539 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1546 =
                     let uu____1552 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1552)  in
                   FStar_Errors.raise_err uu____1546
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1562 =
                (cmd_line_has_impl key) &&
                  (let uu____1565 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1565)
                 in
              if uu____1562
              then
                let uu____1572 = FStar_Options.expose_interfaces ()  in
                (if uu____1572
                 then
                   let uu____1576 =
                     let uu____1578 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____1578  in
                   maybe_use_cache_of uu____1576
                 else
                   (let uu____1585 =
                      let uu____1591 =
                        let uu____1593 =
                          let uu____1595 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____1595  in
                        let uu____1600 =
                          let uu____1602 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____1602  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1593 uu____1600
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1591)
                       in
                    FStar_Errors.raise_err uu____1585))
              else
                (let uu____1612 =
                   let uu____1614 = interface_of file_system_map key  in
                   FStar_Option.get uu____1614  in
                 maybe_use_cache_of uu____1612)
          | PreferInterface key ->
              let uu____1621 = implementation_of file_system_map key  in
              (match uu____1621 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1627 =
                     let uu____1633 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1633)
                      in
                   FStar_Errors.raise_err uu____1627
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____1643 = implementation_of file_system_map key  in
              (match uu____1643 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1649 =
                     let uu____1655 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1655)
                      in
                   FStar_Errors.raise_err uu____1649
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____1665 = implementation_of file_system_map key  in
              (match uu____1665 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1671 =
                     let uu____1677 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1677)
                      in
                   FStar_Errors.raise_err uu____1671
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
          let uu____1738 = deps_try_find deps fn  in
          match uu____1738 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____1746;_} ->
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
    (let uu____1760 =
       let uu____1762 =
         let uu____1764 =
           let uu____1766 =
             let uu____1770 =
               let uu____1774 = deps_keys graph  in
               FStar_List.unique uu____1774  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1788 =
                      let uu____1789 = deps_try_find graph k  in
                      FStar_Util.must uu____1789  in
                    uu____1788.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____1810 =
                      let uu____1812 = lowercase_module_name k  in
                      r uu____1812  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1810
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1770
              in
           FStar_String.concat "\n" uu____1766  in
         FStar_String.op_Hat uu____1764 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____1762  in
     FStar_Util.write_file "dep.graph" uu____1760)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____1833  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1859 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1859  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1899 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1899
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1936 =
              let uu____1942 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1942)  in
            FStar_Errors.raise_err uu____1936)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____2005 = FStar_Util.smap_try_find map1 key  in
      match uu____2005 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2052 = is_interface full_path  in
          if uu____2052
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2101 = is_interface full_path  in
          if uu____2101
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2143 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2161  ->
          match uu____2161 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2143);
    FStar_List.iter
      (fun f  ->
         let uu____2180 = lowercase_module_name f  in add_entry uu____2180 f)
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
        (let uu____2212 =
           let uu____2216 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2216  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2252 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2252  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2212);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2416 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2416 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2439 = string_of_lid l last1  in
      FStar_String.lowercase uu____2439
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2448 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2448
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2470 =
        let uu____2472 =
          let uu____2474 =
            let uu____2476 =
              let uu____2480 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2480  in
            FStar_Util.must uu____2476  in
          FStar_String.lowercase uu____2474  in
        uu____2472 <> k'  in
      if uu____2470
      then
        let uu____2485 = FStar_Ident.range_of_lid lid  in
        let uu____2486 =
          let uu____2492 =
            let uu____2494 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2494 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2492)  in
        FStar_Errors.log_issue uu____2485 uu____2486
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2510 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2532 = FStar_Options.prims_basename ()  in
      let uu____2534 =
        let uu____2538 = FStar_Options.pervasives_basename ()  in
        let uu____2540 =
          let uu____2544 = FStar_Options.pervasives_native_basename ()  in
          [uu____2544]  in
        uu____2538 :: uu____2540  in
      uu____2532 :: uu____2534  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2587 =
         let uu____2590 = lowercase_module_name full_filename  in
         namespace_of_module uu____2590  in
       match uu____2587 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2629 -> d = d'
  
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
        let uu____2669 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____2669
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____2704 =
             let uu____2705 = is_interface filename  in
             if uu____2705
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____2912 =
               let uu____2914 =
                 let uu____2916 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____2916  in
               Prims.op_Negation uu____2914  in
             if uu____2912
             then
               let uu____2985 =
                 let uu____2988 = FStar_ST.op_Bang deps1  in d :: uu____2988
                  in
               FStar_ST.op_Colon_Equals deps1 uu____2985
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____3169 = resolve_module_name original_or_working_map key
                in
             match uu____3169 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____3212 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____3212
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____3251 -> false  in
           let record_open_module let_open lid =
             let uu____3270 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____3270
             then true
             else
               (if let_open
                then
                  (let uu____3279 = FStar_Ident.range_of_lid lid  in
                   let uu____3280 =
                     let uu____3286 =
                       let uu____3288 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____3288
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3286)
                      in
                   FStar_Errors.log_issue uu____3279 uu____3280)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____3308 = FStar_Ident.range_of_lid lid  in
               let uu____3309 =
                 let uu____3315 =
                   let uu____3317 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____3317
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____3315)
                  in
               FStar_Errors.log_issue uu____3308 uu____3309
             else ()  in
           let record_open let_open lid =
             let uu____3337 = record_open_module let_open lid  in
             if uu____3337
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____3354 =
             match uu____3354 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____3361 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____3378 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____3378  in
             let alias = lowercase_join_longident lid true  in
             let uu____3383 = FStar_Util.smap_try_find original_map alias  in
             match uu____3383 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3451 = FStar_Ident.range_of_lid lid  in
                   let uu____3452 =
                     let uu____3458 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3458)
                      in
                   FStar_Errors.log_issue uu____3451 uu____3452);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____3469 = add_dependence_edge working_map module_name  in
             if uu____3469
             then ()
             else
               (let uu____3474 = FStar_Options.debug_any ()  in
                if uu____3474
                then
                  let uu____3477 = FStar_Ident.range_of_lid module_name  in
                  let uu____3478 =
                    let uu____3484 =
                      let uu____3486 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____3486
                       in
                    (FStar_Errors.Warning_UnboundModuleReference, uu____3484)
                     in
                  FStar_Errors.log_issue uu____3477 uu____3478
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____3498 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___14_3626 =
              match uu___14_3626 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____3637 =
                        let uu____3639 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____3639
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____3645) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____3656 =
                        let uu____3658 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____3658
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
                  let uu____3680 =
                    let uu____3681 = lowercase_join_longident lid true  in
                    FriendImplementation uu____3681  in
                  add_dep deps uu____3680
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____3719 = record_module_alias ident lid  in
                  if uu____3719
                  then
                    let uu____3722 =
                      let uu____3723 = lowercase_join_longident lid true  in
                      dep_edge uu____3723  in
                    add_dep deps uu____3722
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____3761,patterms) ->
                  FStar_List.iter
                    (fun uu____3783  ->
                       match uu____3783 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____3792,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____3798,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3800;
                    FStar_Parser_AST.mdest = uu____3801;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3803;
                    FStar_Parser_AST.mdest = uu____3804;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____3806,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3808;
                    FStar_Parser_AST.mdest = uu____3809;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____3813,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____3852  ->
                           match uu____3852 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____3865,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____3872 -> ()
              | FStar_Parser_AST.Pragma uu____3873 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____3909 =
                      let uu____3911 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____3911 > (Prims.parse_int "1")  in
                    if uu____3909
                    then
                      let uu____3958 =
                        let uu____3964 =
                          let uu____3966 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____3966
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____3964)  in
                      let uu____3971 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____3958 uu____3971
                    else ()))
            
            and collect_tycon uu___15_3974 =
              match uu___15_3974 with
              | FStar_Parser_AST.TyconAbstract (uu____3975,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____3987,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____4001,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____4047  ->
                        match uu____4047 with
                        | (uu____4056,t,uu____4058) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____4063,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____4125  ->
                        match uu____4125 with
                        | (uu____4139,t,uu____4141,uu____4142) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___16_4153 =
              match uu___16_4153 with
              | FStar_Parser_AST.DefineEffect (uu____4154,binders,t,decls) ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____4168,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____4181,t);
                   FStar_Parser_AST.brange = uu____4183;
                   FStar_Parser_AST.blevel = uu____4184;
                   FStar_Parser_AST.aqual = uu____4185;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____4188,t);
                   FStar_Parser_AST.brange = uu____4190;
                   FStar_Parser_AST.blevel = uu____4191;
                   FStar_Parser_AST.aqual = uu____4192;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____4196;
                   FStar_Parser_AST.blevel = uu____4197;
                   FStar_Parser_AST.aqual = uu____4198;_} -> collect_term t
               | uu____4201 -> ())
            
            and collect_aqual uu___17_4202 =
              match uu___17_4202 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____4206 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___18_4210 =
              match uu___18_4210 with
              | FStar_Const.Const_int
                  (uu____4211,FStar_Pervasives_Native.Some
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
                  let uu____4238 =
                    let uu____4239 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____4239  in
                  add_dep deps uu____4238
              | FStar_Const.Const_char uu____4275 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____4311 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____4346 -> ()
            
            and collect_term' uu___21_4347 =
              match uu___21_4347 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____4356 =
                      let uu____4358 = FStar_Ident.text_of_id s  in
                      uu____4358 = "@"  in
                    if uu____4356
                    then
                      let uu____4363 =
                        let uu____4364 =
                          let uu____4365 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____4365
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____4364  in
                      collect_term' uu____4363
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____4369 -> ()
              | FStar_Parser_AST.Uvar uu____4370 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____4373) -> record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (if (FStar_List.length termimps) = (Prims.parse_int "1")
                   then record_lid lid
                   else ();
                   FStar_List.iter
                     (fun uu____4407  ->
                        match uu____4407 with
                        | (t,uu____4413) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____4423) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____4425,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____4475  ->
                        match uu____4475 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____4504 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____4514,t1,t2) ->
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
                     (fun uu____4610  ->
                        match uu____4610 with
                        | (uu____4615,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____4618) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___19_4647  ->
                        match uu___19_4647 with
                        | FStar_Util.Inl b -> collect_binder b
                        | FStar_Util.Inr t1 -> collect_term t1) binders;
                   collect_term t)
              | FStar_Parser_AST.QForall (binders,ts,t) ->
                  (collect_binders binders;
                   FStar_List.iter (FStar_List.iter collect_term) ts;
                   collect_term t)
              | FStar_Parser_AST.QExists (binders,ts,t) ->
                  (collect_binders binders;
                   FStar_List.iter (FStar_List.iter collect_term) ts;
                   collect_term t)
              | FStar_Parser_AST.Refine (binder,t) ->
                  (collect_binder binder; collect_term t)
              | FStar_Parser_AST.NamedTyp (uu____4695,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____4699) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____4707) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____4715,uu____4716) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____4722) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____4736 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____4736);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___20_4746  ->
                        match uu___20_4746 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___22_4756 =
              match uu___22_4756 with
              | FStar_Parser_AST.PatVar (uu____4757,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____4763,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____4772 -> ()
              | FStar_Parser_AST.PatConst uu____4773 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____4781 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____4789) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____4810  ->
                       match uu____4810 with
                       | (uu____4815,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____4860 =
              match uu____4860 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____4878 = FStar_Parser_Driver.parse_file filename  in
            match uu____4878 with
            | (ast,uu____4891) ->
                let mname = lowercase_module_name filename  in
                ((let uu____4909 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____4909
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____4948 = FStar_ST.op_Bang deps  in
                  let uu____4996 = FStar_ST.op_Bang mo_roots  in
                  let uu____5044 = FStar_ST.op_Bang has_inline_for_extraction
                     in
                  {
                    direct_deps = uu____4948;
                    additional_roots = uu____4996;
                    has_inline_for_extraction = uu____5044
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____5116 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____5116 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5238 = dep_graph  in
    match uu____5238 with
    | Deps g -> let uu____5242 = FStar_Util.smap_copy g  in Deps uu____5242
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____5387 filename =
              match uu____5387 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____5428 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5428  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5459 = FStar_Options.debug_any ()  in
                         if uu____5459
                         then
                           let uu____5462 =
                             let uu____5464 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____5464  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5462
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___26_5475 = dep_node  in
                           { edges = (uu___26_5475.edges); color = Gray });
                        (let uu____5476 =
                           let uu____5487 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5487
                            in
                         match uu____5476 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___27_5523 = dep_node  in
                                 {
                                   edges = (uu___27_5523.edges);
                                   color = Black
                                 });
                              (let uu____5525 = FStar_Options.debug_any ()
                                  in
                               if uu____5525
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5531 =
                                 let uu____5535 =
                                   FStar_List.collect
                                     (fun uu___23_5542  ->
                                        match uu___23_5542 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____5535 all_friends1
                                  in
                               (uu____5531, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____5608 = FStar_Options.debug_any ()  in
             if uu____5608
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____5637 = deps  in
               match uu____5637 with
               | Deps dg ->
                   let uu____5641 = deps_empty ()  in
                   (match uu____5641 with
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
                                  | uu____5713 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____5721  ->
                                  let uu____5723 =
                                    let uu___28_5724 = dep_node  in
                                    let uu____5725 = widen_one dep_node.edges
                                       in
                                    { edges = uu____5725; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____5723)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____5727 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____5727
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____5732 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____5732 with
             | (friends,all_files_0) ->
                 ((let uu____5775 = FStar_Options.debug_any ()  in
                   if uu____5775
                   then
                     let uu____5778 =
                       let uu____5780 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____5780  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____5778
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____5799 =
                     (let uu____5811 = FStar_Options.debug_any ()  in
                      if uu____5811
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____5799 with
                   | (uu____5834,all_files) ->
                       ((let uu____5849 = FStar_Options.debug_any ()  in
                         if uu____5849
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____5856 = FStar_ST.op_Bang widened  in
                         (all_files, uu____5856))))))
  
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
                let uu____5964 = FStar_Options.find_file fn  in
                match uu____5964 with
                | FStar_Pervasives_Native.None  ->
                    let uu____5970 =
                      let uu____5976 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____5976)
                       in
                    FStar_Errors.raise_err uu____5970
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____6006 =
          let uu____6010 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____6010  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6006  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____6121 =
          let uu____6123 = deps_try_find dep_graph file_name  in
          uu____6123 = FStar_Pervasives_Native.None  in
        if uu____6121
        then
          let uu____6129 =
            let uu____6141 =
              let uu____6155 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____6155 file_name  in
            match uu____6141 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____6129 with
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
                  let uu____6299 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____6299
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____6307 = FStar_List.unique deps1  in
                  { edges = uu____6307; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____6309 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____6309)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____6349 =
            let uu____6355 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____6355)  in
          FStar_Errors.raise_err uu____6349)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____6392 = deps_try_find dep_graph1 filename  in
             match uu____6392 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____6396 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____6396
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____6410 = implementation_of file_system_map f
                            in
                         (match uu____6410 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6421 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____6427 = implementation_of file_system_map f
                            in
                         (match uu____6427 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6438 -> [x; UseImplementation f])
                     | uu____6442 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___29_6445 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____6447 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6447);
                deps_add_dep dep_graph1 filename
                  (let uu___30_6457 = node  in
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
        let uu____6523 =
          let uu____6532 =
            let uu____6534 = FStar_Options.codegen ()  in
            uu____6534 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____6532
           in
        match uu____6523 with
        | (all_files,uu____6547) ->
            ((let uu____6557 = FStar_Options.debug_any ()  in
              if uu____6557
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
  
let (hash_dependences :
  deps ->
    Prims.string ->
      Prims.string ->
        (Prims.string * Prims.string) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun deps  ->
    fun fn  ->
      fun cache_file  ->
        let file_system_map = deps.file_system_map  in
        let all_cmd_line_files = deps.cmd_line_files  in
        let deps1 = deps.dep_graph  in
        let fn1 =
          let uu____6624 = FStar_Options.find_file fn  in
          match uu____6624 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____6632 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____6646 = FStar_Options.debug_any ()  in
           if uu____6646
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____6665 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____6665
          then
            let uu____6676 =
              let uu____6683 =
                let uu____6685 =
                  let uu____6687 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____6687  in
                digest_of_file1 uu____6685  in
              ("interface", uu____6683)  in
            [uu____6676]
          else []  in
        let binary_deps =
          let uu____6719 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____6719
            (FStar_List.filter
               (fun fn2  ->
                  let uu____6734 =
                    (is_interface fn2) &&
                      (let uu____6737 = lowercase_module_name fn2  in
                       uu____6737 = module_name)
                     in
                  Prims.op_Negation uu____6734))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____6753 = lowercase_module_name fn11  in
                 let uu____6755 = lowercase_module_name fn2  in
                 FStar_String.compare uu____6753 uu____6755) binary_deps
           in
        let rec hash_deps out uu___24_6788 =
          match uu___24_6788 with
          | [] ->
              FStar_Pervasives_Native.Some
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____6851 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____6851
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____6869 = FStar_Options.debug_any ()  in
                     if uu____6869
                     then
                       let uu____6872 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____6872
                     else ());
                    FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some dig ->
                   let uu____6888 =
                     let uu____6897 =
                       let uu____6904 = lowercase_module_name fn2  in
                       (uu____6904, dig)  in
                     uu____6897 :: out  in
                   hash_deps uu____6888 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____6944 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____6970  ->
              match uu____6970 with
              | (m,d) ->
                  let uu____6984 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____6984))
       in
    FStar_All.pipe_right uu____6944 (FStar_String.concat "\n")
  
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
              let uu____7019 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____7019 FStar_Option.get  in
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
    let uu____7048 = deps.dep_graph  in
    match uu____7048 with
    | Deps deps1 ->
        let uu____7052 =
          let uu____7054 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____7072 =
                       let uu____7074 =
                         let uu____7076 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____7076
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7074
                        in
                     uu____7072 :: out) []
             in
          FStar_All.pipe_right uu____7054 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____7052 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____7148 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7148) ||
          (let uu____7155 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7155)
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
            let uu____7198 =
              let uu____7202 = FStar_ST.op_Bang order  in ml_file ::
                uu____7202
               in
            FStar_ST.op_Colon_Equals order uu____7198
         in
      let rec aux uu___25_7309 =
        match uu___25_7309 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7337 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7337 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7340 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7340
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7344;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7353 = should_visit lc_module_name  in
              if uu____7353
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7361 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____7361);
                 (let uu____7366 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____7366);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7378 = FStar_ST.op_Bang order  in FStar_List.rev uu____7378)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7452 =
          let uu____7454 =
            let uu____7458 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7458  in
          FStar_Option.get uu____7454  in
        FStar_Util.replace_chars uu____7452 46 "_"  in
      let uu____7463 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____7463  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7485 = output_file ".ml" f  in norm_path uu____7485  in
    let output_krml_file f =
      let uu____7497 = output_file ".krml" f  in norm_path uu____7497  in
    let output_cmx_file f =
      let uu____7509 = output_file ".cmx" f  in norm_path uu____7509  in
    let cache_file f =
      let uu____7526 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____7526
        (fun uu____7555  ->
           match uu____7555 with | (f1,b) -> ((norm_path f1), b))
       in
    let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")  in
    let set_of_unchecked_files =
      let uu____7606 =
        let uu____7617 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____7656 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____7656 FStar_Option.get  in
               let iface_deps =
                 let uu____7666 = is_interface file_name  in
                 if uu____7666
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____7677 =
                      let uu____7681 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____7681  in
                    match uu____7677 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____7693 =
                          let uu____7696 =
                            let uu____7697 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____7697  in
                          uu____7696.edges  in
                        FStar_Pervasives_Native.Some uu____7693)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____7714 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____7714))
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
               let files4 = FStar_String.concat "\\\n\t" files3  in
               let uu____7773 = cache_file file_name  in
               match uu____7773 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let already_there =
                       let uu____7806 =
                         let uu____7820 =
                           let uu____7822 = output_file ".krml" file_name  in
                           norm_path uu____7822  in
                         FStar_Util.smap_try_find transitive_krml uu____7820
                          in
                       match uu____7806 with
                       | FStar_Pervasives_Native.Some
                           (uu____7839,already_there,uu____7841) ->
                           already_there
                       | FStar_Pervasives_Native.None  -> []  in
                     (let uu____7876 =
                        let uu____7878 = output_file ".krml" file_name  in
                        norm_path uu____7878  in
                      let uu____7881 =
                        let uu____7893 =
                          let uu____7895 = output_file ".exe" file_name  in
                          norm_path uu____7895  in
                        let uu____7898 =
                          let uu____7902 =
                            let uu____7906 =
                              let uu____7910 = deps_of deps file_name  in
                              FStar_List.map
                                (fun x  ->
                                   let uu____7920 = output_file ".krml" x  in
                                   norm_path uu____7920) uu____7910
                               in
                            FStar_List.append already_there uu____7906  in
                          FStar_List.unique uu____7902  in
                        (uu____7893, uu____7898, false)  in
                      FStar_Util.smap_add transitive_krml uu____7876
                        uu____7881);
                     (let uu____7942 =
                        let uu____7951 = FStar_Options.cmi ()  in
                        if uu____7951
                        then
                          topological_dependences_of deps.file_system_map
                            deps.dep_graph deps.interfaces_with_inlining
                            [file_name] true
                        else
                          (let maybe_widen_deps f_deps =
                             FStar_List.map
                               (fun dep1  ->
                                  file_of_dep_aux false deps.file_system_map
                                    deps.cmd_line_files dep1) f_deps
                              in
                           let fst_files = maybe_widen_deps dep_node.edges
                              in
                           let fst_files_from_iface =
                             match iface_deps1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some iface_deps2 ->
                                 maybe_widen_deps iface_deps2
                              in
                           let uu____7999 =
                             FStar_Util.remove_dups
                               (fun x  -> fun y  -> x = y)
                               (FStar_List.append fst_files
                                  fst_files_from_iface)
                              in
                           (uu____7999, false))
                         in
                      match uu____7942 with
                      | (all_fst_files_dep,widened) ->
                          let all_checked_fst_dep_files =
                            FStar_All.pipe_right all_fst_files_dep
                              (FStar_List.map
                                 (fun f  ->
                                    let uu____8046 =
                                      FStar_All.pipe_right f cache_file  in
                                    FStar_All.pipe_right uu____8046
                                      FStar_Pervasives_Native.fst))
                             in
                          ((let uu____8070 = is_implementation file_name  in
                            if uu____8070
                            then
                              ((let uu____8074 =
                                  (FStar_Options.cmi ()) && widened  in
                                if uu____8074
                                then
                                  ((let uu____8078 = output_ml_file file_name
                                       in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____8078 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files));
                                   (let uu____8082 =
                                      output_krml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____8082 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files)))
                                else
                                  ((let uu____8089 = output_ml_file file_name
                                       in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____8089 cache_file_name1);
                                   (let uu____8092 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s\n\n" uu____8092
                                      cache_file_name1)));
                               (let cmx_files =
                                  let extracted_fst_files =
                                    FStar_All.pipe_right all_fst_files_dep
                                      (FStar_List.filter
                                         (fun df  ->
                                            (let uu____8117 =
                                               lowercase_module_name df  in
                                             let uu____8119 =
                                               lowercase_module_name
                                                 file_name
                                                in
                                             uu____8117 <> uu____8119) &&
                                              (let uu____8123 =
                                                 lowercase_module_name df  in
                                               FStar_Options.should_extract
                                                 uu____8123)))
                                     in
                                  FStar_All.pipe_right extracted_fst_files
                                    (FStar_List.map output_cmx_file)
                                   in
                                let uu____8133 =
                                  let uu____8135 =
                                    lowercase_module_name file_name  in
                                  FStar_Options.should_extract uu____8135  in
                                if uu____8133
                                then
                                  let uu____8138 = output_cmx_file file_name
                                     in
                                  let uu____8140 = output_ml_file file_name
                                     in
                                  FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                    uu____8138 uu____8140
                                    (FStar_String.concat "\\\n\t" cmx_files)
                                else ()))
                            else
                              (let uu____8148 =
                                 (let uu____8152 =
                                    let uu____8154 =
                                      lowercase_module_name file_name  in
                                    has_implementation deps.file_system_map
                                      uu____8154
                                     in
                                  Prims.op_Negation uu____8152) &&
                                   (is_interface file_name)
                                  in
                               if uu____8148
                               then
                                 let uu____8157 =
                                   (FStar_Options.cmi ()) && widened  in
                                 (if uu____8157
                                  then
                                    let uu____8160 =
                                      output_krml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____8160 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files)
                                  else
                                    (let uu____8166 =
                                       output_krml_file file_name  in
                                     FStar_Util.print2 "%s: %s \n\n"
                                       uu____8166 cache_file_name1))
                               else ()));
                           set_of_unchecked_files1))))) uu____7617
         in
      FStar_All.pipe_right keys uu____7606  in
    let uu____8177 =
      let uu____8188 =
        let uu____8192 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____8192
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____8188
        (fun l  ->
           let uu____8229 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____8229))
       in
    match uu____8177 with
    | (all_fst_files,all_unchecked_fst_files) ->
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8287 = FStar_Options.should_extract mname  in
                  if uu____8287
                  then
                    let uu____8290 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____8290
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8317 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____8317));
          sort_output_files krml_file_map  in
        let rec make_transitive f =
          let uu____8336 =
            let uu____8348 = FStar_Util.smap_try_find transitive_krml f  in
            FStar_Util.must uu____8348  in
          match uu____8336 with
          | (exe,deps1,seen) ->
              if seen
              then (exe, deps1)
              else
                (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                 (let deps2 =
                    let uu____8442 =
                      let uu____8446 =
                        FStar_List.map
                          (fun dep1  ->
                             let uu____8462 = make_transitive dep1  in
                             match uu____8462 with
                             | (uu____8474,deps2) -> dep1 :: deps2) deps1
                         in
                      FStar_List.flatten uu____8446  in
                    FStar_List.unique uu____8442  in
                  FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                  (exe, deps2)))
           in
        ((let uu____8510 = FStar_Util.smap_keys transitive_krml  in
          FStar_List.iter
            (fun f  ->
               let uu____8535 = make_transitive f  in
               match uu____8535 with
               | (exe,deps1) ->
                   let deps2 =
                     let uu____8556 = FStar_List.unique (f :: deps1)  in
                     FStar_String.concat " " uu____8556  in
                   let wasm =
                     let uu____8565 =
                       FStar_Util.substring exe (Prims.parse_int "0")
                         ((FStar_String.length exe) - (Prims.parse_int "4"))
                        in
                     FStar_String.op_Hat uu____8565 ".wasm"  in
                   (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                    FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____8510);
         (let uu____8574 =
            let uu____8576 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8576 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____8574);
         (let uu____8595 =
            let uu____8597 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8597 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n" uu____8595);
         (let uu____8616 =
            let uu____8618 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8618 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____8616);
         (let uu____8636 =
            let uu____8638 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8638 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____8636))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____8662 = FStar_Options.dep ()  in
    match uu____8662 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8674 ->
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
         fun uu____8729  ->
           fun s  ->
             match uu____8729 with
             | (v0,v1) ->
                 let uu____8758 =
                   let uu____8760 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____8760  in
                 FStar_String.op_Hat s uu____8758) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8781 =
        let uu____8783 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8783  in
      has_interface deps.file_system_map uu____8781
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8799 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8799  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8810 =
                   let uu____8812 = module_name_of_file f  in
                   FStar_String.lowercase uu____8812  in
                 uu____8810 = m)))
  