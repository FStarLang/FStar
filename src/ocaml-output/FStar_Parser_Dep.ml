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
  fun uu___26_270  ->
    match uu___26_270 with
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
  fun uu___27_505  ->
    match uu___27_505 with
    | UseInterface f -> Prims.strcat "UseInterface " f
    | PreferInterface f -> Prims.strcat "PreferInterface " f
    | UseImplementation f -> Prims.strcat "UseImplementation " f
    | FriendImplementation f -> Prims.strcat "FriendImplementation " f
  
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
  (dependence Prims.list * dependence Prims.list * Prims.bool)
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
  fun uu____806  ->
    fun k  -> match uu____806 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____828  ->
    fun k  ->
      fun v1  -> match uu____828 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____843  -> match uu____843 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____855  ->
    let uu____856 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____856
  
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
  let uu____914 = deps_empty ()  in
  let uu____915 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____927 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____914 uu____915 [] [] [] uu____927 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___28_940  ->
    match uu___28_940 with
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
      let uu____969 = FStar_Util.smap_try_find file_system_map key  in
      match uu____969 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____996) ->
          let uu____1018 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1018
      | FStar_Pervasives_Native.Some
          (uu____1021,FStar_Pervasives_Native.Some fn) ->
          let uu____1044 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1044
      | uu____1047 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1080 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1080 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1107) ->
          FStar_Pervasives_Native.Some iface
      | uu____1130 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1163 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1163 with
      | FStar_Pervasives_Native.Some
          (uu____1189,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1213 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1242 = interface_of file_system_map key  in
      FStar_Option.isSome uu____1242
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1262 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____1262
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____1289 =
        let uu____1291 = FStar_Options.lax ()  in
        if uu____1291 then ".checked.lax" else ".checked"  in
      Prims.strcat fn uu____1289  in
    let uu____1299 =
      let uu____1303 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1303  in
    match uu____1299 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____1324 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1324
        then
          let uu____1335 =
            let uu____1341 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1341)
             in
          FStar_Errors.raise_err uu____1335
        else
          (let uu____1353 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____1353, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____1367 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____1367 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1403 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1403 FStar_Util.must
  
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
                      (let uu____1457 = lowercase_module_name fn  in
                       key = uu____1457)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1476 = interface_of file_system_map key  in
              (match uu____1476 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1483 =
                     let uu____1489 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1489)  in
                   FStar_Errors.raise_err uu____1483
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1499 =
                (cmd_line_has_impl key) &&
                  (let uu____1502 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1502)
                 in
              if uu____1499
              then
                let uu____1509 = FStar_Options.expose_interfaces ()  in
                (if uu____1509
                 then
                   let uu____1513 =
                     let uu____1515 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____1515  in
                   maybe_use_cache_of uu____1513
                 else
                   (let uu____1522 =
                      let uu____1528 =
                        let uu____1530 =
                          let uu____1532 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____1532  in
                        let uu____1537 =
                          let uu____1539 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____1539  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1530 uu____1537
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1528)
                       in
                    FStar_Errors.raise_err uu____1522))
              else
                (let uu____1549 =
                   let uu____1551 = interface_of file_system_map key  in
                   FStar_Option.get uu____1551  in
                 maybe_use_cache_of uu____1549)
          | PreferInterface key ->
              let uu____1558 = implementation_of file_system_map key  in
              (match uu____1558 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1564 =
                     let uu____1570 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1570)
                      in
                   FStar_Errors.raise_err uu____1564
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____1580 = implementation_of file_system_map key  in
              (match uu____1580 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1586 =
                     let uu____1592 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1592)
                      in
                   FStar_Errors.raise_err uu____1586
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____1602 = implementation_of file_system_map key  in
              (match uu____1602 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1608 =
                     let uu____1614 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1614)
                      in
                   FStar_Errors.raise_err uu____1608
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
          let uu____1675 = deps_try_find deps fn  in
          match uu____1675 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____1683;_} ->
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
    (let uu____1697 =
       let uu____1699 =
         let uu____1701 =
           let uu____1703 =
             let uu____1707 =
               let uu____1711 = deps_keys graph  in
               FStar_List.unique uu____1711  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1725 =
                      let uu____1726 = deps_try_find graph k  in
                      FStar_Util.must uu____1726  in
                    uu____1725.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____1747 =
                      let uu____1749 = lowercase_module_name k  in
                      r uu____1749  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1747
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1707
              in
           FStar_String.concat "\n" uu____1703  in
         Prims.strcat uu____1701 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1699  in
     FStar_Util.write_file "dep.graph" uu____1697)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____1770  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1796 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1796  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1836 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1836
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1873 =
              let uu____1879 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1879)  in
            FStar_Errors.raise_err uu____1873)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1942 = FStar_Util.smap_try_find map1 key  in
      match uu____1942 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1989 = is_interface full_path  in
          if uu____1989
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2038 = is_interface full_path  in
          if uu____2038
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2080 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2098  ->
          match uu____2098 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2080);
    FStar_List.iter
      (fun f  ->
         let uu____2117 = lowercase_module_name f  in add_entry uu____2117 f)
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
        let prefix2 = Prims.strcat prefix1 "."  in
        (let uu____2149 =
           let uu____2153 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2153  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2189 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2189  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2149);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2353 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2353 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2376 = string_of_lid l last1  in
      FStar_String.lowercase uu____2376
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2385 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2385
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2407 =
        let uu____2409 =
          let uu____2411 =
            let uu____2413 =
              let uu____2417 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2417  in
            FStar_Util.must uu____2413  in
          FStar_String.lowercase uu____2411  in
        uu____2409 <> k'  in
      if uu____2407
      then
        let uu____2422 = FStar_Ident.range_of_lid lid  in
        let uu____2423 =
          let uu____2429 =
            let uu____2431 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2431 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2429)  in
        FStar_Errors.log_issue uu____2422 uu____2423
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2447 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2469 = FStar_Options.prims_basename ()  in
      let uu____2471 =
        let uu____2475 = FStar_Options.pervasives_basename ()  in
        let uu____2477 =
          let uu____2481 = FStar_Options.pervasives_native_basename ()  in
          [uu____2481]  in
        uu____2475 :: uu____2477  in
      uu____2469 :: uu____2471  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2524 =
         let uu____2527 = lowercase_module_name full_filename  in
         namespace_of_module uu____2527  in
       match uu____2524 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2566 -> d = d'
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        (dependence Prims.list * dependence Prims.list * Prims.bool))
  =
  fun original_map  ->
    fun filename  ->
      fun get_parsing_data_from_cache  ->
        let from_cache = get_parsing_data_from_cache filename  in
        let uu____2625 = FStar_All.pipe_right from_cache FStar_Util.is_some
           in
        if uu____2625
        then FStar_All.pipe_right from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____2682 =
             let uu____2683 = is_interface filename  in
             if uu____2683
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____2890 =
               let uu____2892 =
                 let uu____2894 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____2894  in
               Prims.op_Negation uu____2892  in
             if uu____2890
             then
               let uu____2963 =
                 let uu____2966 = FStar_ST.op_Bang deps1  in d :: uu____2966
                  in
               FStar_ST.op_Colon_Equals deps1 uu____2963
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____3147 = resolve_module_name original_or_working_map key
                in
             match uu____3147 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____3190 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____3190
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____3229 -> false  in
           let record_open_module let_open lid =
             let uu____3248 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____3248
             then true
             else
               (if let_open
                then
                  (let uu____3257 = FStar_Ident.range_of_lid lid  in
                   let uu____3258 =
                     let uu____3264 =
                       let uu____3266 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____3266
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3264)
                      in
                   FStar_Errors.log_issue uu____3257 uu____3258)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____3286 = FStar_Ident.range_of_lid lid  in
               let uu____3287 =
                 let uu____3293 =
                   let uu____3295 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____3295
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____3293)
                  in
               FStar_Errors.log_issue uu____3286 uu____3287
             else ()  in
           let record_open let_open lid =
             let uu____3315 = record_open_module let_open lid  in
             if uu____3315
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____3332 =
             match uu____3332 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____3339 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____3356 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____3356  in
             let alias = lowercase_join_longident lid true  in
             let uu____3361 = FStar_Util.smap_try_find original_map alias  in
             match uu____3361 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3429 = FStar_Ident.range_of_lid lid  in
                   let uu____3430 =
                     let uu____3436 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3436)
                      in
                   FStar_Errors.log_issue uu____3429 uu____3430);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____3447 = add_dependence_edge working_map module_name  in
             if uu____3447
             then ()
             else
               (let uu____3452 = FStar_Options.debug_any ()  in
                if uu____3452
                then
                  let uu____3455 = FStar_Ident.range_of_lid module_name  in
                  let uu____3456 =
                    let uu____3462 =
                      let uu____3464 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____3464
                       in
                    (FStar_Errors.Warning_UnboundModuleReference, uu____3462)
                     in
                  FStar_Errors.log_issue uu____3455 uu____3456
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____3476 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___29_3604 =
              match uu___29_3604 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____3615 =
                        let uu____3617 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____3617
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____3623) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____3634 =
                        let uu____3636 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____3636
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
                  let uu____3658 =
                    let uu____3659 = lowercase_join_longident lid true  in
                    FriendImplementation uu____3659  in
                  add_dep deps uu____3658
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____3697 = record_module_alias ident lid  in
                  if uu____3697
                  then
                    let uu____3700 =
                      let uu____3701 = lowercase_join_longident lid true  in
                      dep_edge uu____3701  in
                    add_dep deps uu____3700
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____3739,patterms) ->
                  FStar_List.iter
                    (fun uu____3761  ->
                       match uu____3761 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____3770,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____3776,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3778;
                    FStar_Parser_AST.mdest = uu____3779;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3781;
                    FStar_Parser_AST.mdest = uu____3782;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____3784,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3786;
                    FStar_Parser_AST.mdest = uu____3787;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____3791,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____3830  ->
                           match uu____3830 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____3843,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____3850 -> ()
              | FStar_Parser_AST.Pragma uu____3851 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____3887 =
                      let uu____3889 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____3889 > (Prims.parse_int "1")  in
                    if uu____3887
                    then
                      let uu____3936 =
                        let uu____3942 =
                          let uu____3944 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____3944
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____3942)  in
                      let uu____3949 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____3936 uu____3949
                    else ()))
            
            and collect_tycon uu___30_3952 =
              match uu___30_3952 with
              | FStar_Parser_AST.TyconAbstract (uu____3953,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____3965,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____3979,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____4025  ->
                        match uu____4025 with
                        | (uu____4034,t,uu____4036) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____4041,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____4103  ->
                        match uu____4103 with
                        | (uu____4117,t,uu____4119,uu____4120) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___31_4131 =
              match uu___31_4131 with
              | FStar_Parser_AST.DefineEffect (uu____4132,binders,t,decls) ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____4146,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____4159,t);
                   FStar_Parser_AST.brange = uu____4161;
                   FStar_Parser_AST.blevel = uu____4162;
                   FStar_Parser_AST.aqual = uu____4163;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____4166,t);
                   FStar_Parser_AST.brange = uu____4168;
                   FStar_Parser_AST.blevel = uu____4169;
                   FStar_Parser_AST.aqual = uu____4170;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____4174;
                   FStar_Parser_AST.blevel = uu____4175;
                   FStar_Parser_AST.aqual = uu____4176;_} -> collect_term t
               | uu____4179 -> ())
            
            and collect_aqual uu___32_4180 =
              match uu___32_4180 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____4184 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___33_4188 =
              match uu___33_4188 with
              | FStar_Const.Const_int
                  (uu____4189,FStar_Pervasives_Native.Some
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
                  let uu____4216 =
                    let uu____4217 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____4217  in
                  add_dep deps uu____4216
              | FStar_Const.Const_char uu____4253 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____4289 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____4324 -> ()
            
            and collect_term' uu___36_4325 =
              match uu___36_4325 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____4334 =
                      let uu____4336 = FStar_Ident.text_of_id s  in
                      uu____4336 = "@"  in
                    if uu____4334
                    then
                      let uu____4341 =
                        let uu____4342 =
                          let uu____4343 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____4343
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____4342  in
                      collect_term' uu____4341
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____4347 -> ()
              | FStar_Parser_AST.Uvar uu____4348 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____4351) -> record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (if (FStar_List.length termimps) = (Prims.parse_int "1")
                   then record_lid lid
                   else ();
                   FStar_List.iter
                     (fun uu____4385  ->
                        match uu____4385 with
                        | (t,uu____4391) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____4401) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____4403,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____4453  ->
                        match uu____4453 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____4482 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____4492,t1,t2) ->
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
                     (fun uu____4588  ->
                        match uu____4588 with
                        | (uu____4593,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____4596) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___34_4625  ->
                        match uu___34_4625 with
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
              | FStar_Parser_AST.NamedTyp (uu____4673,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____4677) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____4685) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____4693,uu____4694) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____4700) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____4714 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____4714);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___35_4724  ->
                        match uu___35_4724 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___37_4734 =
              match uu___37_4734 with
              | FStar_Parser_AST.PatVar (uu____4735,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____4741,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____4750 -> ()
              | FStar_Parser_AST.PatConst uu____4751 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____4759 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____4767) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____4788  ->
                       match uu____4788 with
                       | (uu____4793,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____4838 =
              match uu____4838 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____4856 = FStar_Parser_Driver.parse_file filename  in
            match uu____4856 with
            | (ast,uu____4880) ->
                let mname = lowercase_module_name filename  in
                ((let uu____4898 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____4898
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____4937 = FStar_ST.op_Bang deps  in
                  let uu____4985 = FStar_ST.op_Bang mo_roots  in
                  let uu____5033 = FStar_ST.op_Bang has_inline_for_extraction
                     in
                  (uu____4937, uu____4985, uu____5033)))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____5110 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____5110 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5232 = dep_graph  in
    match uu____5232 with
    | Deps g -> let uu____5236 = FStar_Util.smap_copy g  in Deps uu____5236
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____5381 filename =
              match uu____5381 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____5422 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5422  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5453 = FStar_Options.debug_any ()  in
                         if uu____5453
                         then
                           let uu____5456 =
                             let uu____5458 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____5458  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5456
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___41_5469 = dep_node  in
                           { edges = (uu___41_5469.edges); color = Gray });
                        (let uu____5470 =
                           let uu____5481 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5481
                            in
                         match uu____5470 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___42_5517 = dep_node  in
                                 {
                                   edges = (uu___42_5517.edges);
                                   color = Black
                                 });
                              (let uu____5519 = FStar_Options.debug_any ()
                                  in
                               if uu____5519
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5525 =
                                 let uu____5529 =
                                   FStar_List.collect
                                     (fun uu___38_5536  ->
                                        match uu___38_5536 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____5529 all_friends1
                                  in
                               (uu____5525, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____5602 = FStar_Options.debug_any ()  in
             if uu____5602
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____5631 = deps  in
               match uu____5631 with
               | Deps dg ->
                   let uu____5635 = deps_empty ()  in
                   (match uu____5635 with
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
                                  | uu____5707 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____5715  ->
                                  let uu____5717 =
                                    let uu___43_5718 = dep_node  in
                                    let uu____5719 = widen_one dep_node.edges
                                       in
                                    { edges = uu____5719; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____5717)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____5721 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____5721
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____5726 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____5726 with
             | (friends,all_files_0) ->
                 ((let uu____5769 = FStar_Options.debug_any ()  in
                   if uu____5769
                   then
                     let uu____5772 =
                       let uu____5774 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____5774  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____5772
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____5793 =
                     (let uu____5805 = FStar_Options.debug_any ()  in
                      if uu____5805
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____5793 with
                   | (uu____5828,all_files) ->
                       ((let uu____5843 = FStar_Options.debug_any ()  in
                         if uu____5843
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____5850 = FStar_ST.op_Bang widened  in
                         (all_files, uu____5850))))))
  
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
                let uu____5958 = FStar_Options.find_file fn  in
                match uu____5958 with
                | FStar_Pervasives_Native.None  ->
                    let uu____5964 =
                      let uu____5970 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____5970)
                       in
                    FStar_Errors.raise_err uu____5964
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____6000 =
          let uu____6004 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____6004  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6000  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____6137 =
          let uu____6139 = deps_try_find dep_graph file_name  in
          uu____6139 = FStar_Pervasives_Native.None  in
        if uu____6137
        then
          let uu____6145 =
            let uu____6157 =
              let uu____6171 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____6171 file_name  in
            match uu____6157 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                collect_one file_system_map file_name
                  get_parsing_data_from_cache
             in
          match uu____6145 with
          | (deps,mo_roots,needs_interface_inlining) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name
                 (deps, mo_roots, needs_interface_inlining);
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____6325 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____6325
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____6333 = FStar_List.unique deps1  in
                  { edges = uu____6333; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____6335 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____6335)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____6375 =
            let uu____6381 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____6381)  in
          FStar_Errors.raise_err uu____6375)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____6418 = deps_try_find dep_graph1 filename  in
             match uu____6418 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____6422 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____6422
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____6436 = implementation_of file_system_map f
                            in
                         (match uu____6436 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6447 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____6453 = implementation_of file_system_map f
                            in
                         (match uu____6453 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6464 -> [x; UseImplementation f])
                     | uu____6468 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___44_6471 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____6473 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6473);
                deps_add_dep dep_graph1 filename
                  (let uu___45_6483 = node  in
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
        let uu____6549 =
          let uu____6558 =
            let uu____6560 = FStar_Options.codegen ()  in
            uu____6560 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____6558
           in
        match uu____6549 with
        | (all_files,uu____6573) ->
            ((let uu____6583 = FStar_Options.debug_any ()  in
              if uu____6583
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
          let uu____6650 = FStar_Options.find_file fn  in
          match uu____6650 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____6658 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____6672 = FStar_Options.debug_any ()  in
           if uu____6672
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____6691 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____6691
          then
            let uu____6702 =
              let uu____6709 =
                let uu____6711 =
                  let uu____6713 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____6713  in
                digest_of_file1 uu____6711  in
              ("interface", uu____6709)  in
            [uu____6702]
          else []  in
        let binary_deps =
          let uu____6745 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____6745
            (FStar_List.filter
               (fun fn2  ->
                  let uu____6760 =
                    (is_interface fn2) &&
                      (let uu____6763 = lowercase_module_name fn2  in
                       uu____6763 = module_name)
                     in
                  Prims.op_Negation uu____6760))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____6779 = lowercase_module_name fn11  in
                 let uu____6781 = lowercase_module_name fn2  in
                 FStar_String.compare uu____6779 uu____6781) binary_deps
           in
        let rec hash_deps out uu___39_6814 =
          match uu___39_6814 with
          | [] ->
              FStar_Pervasives_Native.Some
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____6877 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____6877
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____6895 = FStar_Options.debug_any ()  in
                     if uu____6895
                     then
                       let uu____6898 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____6898
                     else ());
                    FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some dig ->
                   let uu____6914 =
                     let uu____6923 =
                       let uu____6930 = lowercase_module_name fn2  in
                       (uu____6930, dig)  in
                     uu____6923 :: out  in
                   hash_deps uu____6914 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____6970 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____6996  ->
              match uu____6996 with
              | (m,d) ->
                  let uu____7010 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____7010))
       in
    FStar_All.pipe_right uu____6970 (FStar_String.concat "\n")
  
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
              let uu____7045 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____7045 FStar_Option.get  in
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
    let uu____7074 = deps.dep_graph  in
    match uu____7074 with
    | Deps deps1 ->
        let uu____7078 =
          let uu____7080 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____7098 =
                       let uu____7100 =
                         let uu____7102 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____7102
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7100
                        in
                     uu____7098 :: out) []
             in
          FStar_All.pipe_right uu____7080 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____7078 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____7174 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7174) ||
          (let uu____7181 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7181)
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
            let uu____7224 =
              let uu____7228 = FStar_ST.op_Bang order  in ml_file ::
                uu____7228
               in
            FStar_ST.op_Colon_Equals order uu____7224
         in
      let rec aux uu___40_7335 =
        match uu___40_7335 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7363 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7363 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7366 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7366
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7370;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7379 = should_visit lc_module_name  in
              if uu____7379
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7387 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____7387);
                 (let uu____7392 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____7392);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7404 = FStar_ST.op_Bang order  in FStar_List.rev uu____7404)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7478 =
          let uu____7480 =
            let uu____7484 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7484  in
          FStar_Option.get uu____7480  in
        FStar_Util.replace_chars uu____7478 46 "_"  in
      FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7509 = output_file ".ml" f  in norm_path uu____7509  in
    let output_krml_file f =
      let uu____7521 = output_file ".krml" f  in norm_path uu____7521  in
    let output_cmx_file f =
      let uu____7533 = output_file ".cmx" f  in norm_path uu____7533  in
    let cache_file f =
      let uu____7550 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____7550
        (fun uu____7579  ->
           match uu____7579 with | (f1,b) -> ((norm_path f1), b))
       in
    let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")  in
    let set_of_unchecked_files =
      let uu____7630 =
        let uu____7641 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____7680 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____7680 FStar_Option.get  in
               let iface_deps =
                 let uu____7690 = is_interface file_name  in
                 if uu____7690
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____7701 =
                      let uu____7705 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____7705  in
                    match uu____7701 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____7717 =
                          let uu____7720 =
                            let uu____7721 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____7721  in
                          uu____7720.edges  in
                        FStar_Pervasives_Native.Some uu____7717)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____7738 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____7738))
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
               let uu____7797 = cache_file file_name  in
               match uu____7797 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let already_there =
                       let uu____7830 =
                         let uu____7844 =
                           let uu____7846 = output_file ".krml" file_name  in
                           norm_path uu____7846  in
                         FStar_Util.smap_try_find transitive_krml uu____7844
                          in
                       match uu____7830 with
                       | FStar_Pervasives_Native.Some
                           (uu____7863,already_there,uu____7865) ->
                           already_there
                       | FStar_Pervasives_Native.None  -> []  in
                     (let uu____7900 =
                        let uu____7902 = output_file ".krml" file_name  in
                        norm_path uu____7902  in
                      let uu____7905 =
                        let uu____7917 =
                          let uu____7919 = output_file ".exe" file_name  in
                          norm_path uu____7919  in
                        let uu____7922 =
                          let uu____7926 =
                            let uu____7930 =
                              let uu____7934 = deps_of deps file_name  in
                              FStar_List.map
                                (fun x  ->
                                   let uu____7944 = output_file ".krml" x  in
                                   norm_path uu____7944) uu____7934
                               in
                            FStar_List.append already_there uu____7930  in
                          FStar_List.unique uu____7926  in
                        (uu____7917, uu____7922, false)  in
                      FStar_Util.smap_add transitive_krml uu____7900
                        uu____7905);
                     (let uu____7966 =
                        let uu____7975 = FStar_Options.cmi ()  in
                        if uu____7975
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
                           let uu____8023 =
                             FStar_Util.remove_dups
                               (fun x  -> fun y  -> x = y)
                               (FStar_List.append fst_files
                                  fst_files_from_iface)
                              in
                           (uu____8023, false))
                         in
                      match uu____7966 with
                      | (all_fst_files_dep,widened) ->
                          let all_checked_fst_dep_files =
                            FStar_All.pipe_right all_fst_files_dep
                              (FStar_List.map
                                 (fun f  ->
                                    let uu____8070 =
                                      FStar_All.pipe_right f cache_file  in
                                    FStar_All.pipe_right uu____8070
                                      FStar_Pervasives_Native.fst))
                             in
                          ((let uu____8094 = is_implementation file_name  in
                            if uu____8094
                            then
                              ((let uu____8098 =
                                  (FStar_Options.cmi ()) && widened  in
                                if uu____8098
                                then
                                  ((let uu____8102 = output_ml_file file_name
                                       in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____8102 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files));
                                   (let uu____8106 =
                                      output_krml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____8106 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files)))
                                else
                                  ((let uu____8113 = output_ml_file file_name
                                       in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____8113 cache_file_name1);
                                   (let uu____8116 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s\n\n" uu____8116
                                      cache_file_name1)));
                               (let cmx_files =
                                  let extracted_fst_files =
                                    FStar_All.pipe_right all_fst_files_dep
                                      (FStar_List.filter
                                         (fun df  ->
                                            (let uu____8141 =
                                               lowercase_module_name df  in
                                             let uu____8143 =
                                               lowercase_module_name
                                                 file_name
                                                in
                                             uu____8141 <> uu____8143) &&
                                              (let uu____8147 =
                                                 lowercase_module_name df  in
                                               FStar_Options.should_extract
                                                 uu____8147)))
                                     in
                                  FStar_All.pipe_right extracted_fst_files
                                    (FStar_List.map output_cmx_file)
                                   in
                                let uu____8157 =
                                  let uu____8159 =
                                    lowercase_module_name file_name  in
                                  FStar_Options.should_extract uu____8159  in
                                if uu____8157
                                then
                                  let uu____8162 = output_cmx_file file_name
                                     in
                                  let uu____8164 = output_ml_file file_name
                                     in
                                  FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                    uu____8162 uu____8164
                                    (FStar_String.concat "\\\n\t" cmx_files)
                                else ()))
                            else
                              (let uu____8172 =
                                 (let uu____8176 =
                                    let uu____8178 =
                                      lowercase_module_name file_name  in
                                    has_implementation deps.file_system_map
                                      uu____8178
                                     in
                                  Prims.op_Negation uu____8176) &&
                                   (is_interface file_name)
                                  in
                               if uu____8172
                               then
                                 let uu____8181 =
                                   (FStar_Options.cmi ()) && widened  in
                                 (if uu____8181
                                  then
                                    let uu____8184 =
                                      output_krml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____8184 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files)
                                  else
                                    (let uu____8190 =
                                       output_krml_file file_name  in
                                     FStar_Util.print2 "%s: %s \n\n"
                                       uu____8190 cache_file_name1))
                               else ()));
                           set_of_unchecked_files1))))) uu____7641
         in
      FStar_All.pipe_right keys uu____7630  in
    let uu____8201 =
      let uu____8212 =
        let uu____8216 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____8216
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____8212
        (fun l  ->
           let uu____8253 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____8253))
       in
    match uu____8201 with
    | (all_fst_files,all_unchecked_fst_files) ->
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8311 = FStar_Options.should_extract mname  in
                  if uu____8311
                  then
                    let uu____8314 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____8314
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8341 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____8341));
          sort_output_files krml_file_map  in
        let rec make_transitive f =
          let uu____8360 =
            let uu____8372 = FStar_Util.smap_try_find transitive_krml f  in
            FStar_Util.must uu____8372  in
          match uu____8360 with
          | (exe,deps1,seen) ->
              if seen
              then (exe, deps1)
              else
                (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                 (let deps2 =
                    let uu____8466 =
                      let uu____8470 =
                        FStar_List.map
                          (fun dep1  ->
                             let uu____8486 = make_transitive dep1  in
                             match uu____8486 with
                             | (uu____8498,deps2) -> dep1 :: deps2) deps1
                         in
                      FStar_List.flatten uu____8470  in
                    FStar_List.unique uu____8466  in
                  FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                  (exe, deps2)))
           in
        ((let uu____8534 = FStar_Util.smap_keys transitive_krml  in
          FStar_List.iter
            (fun f  ->
               let uu____8559 = make_transitive f  in
               match uu____8559 with
               | (exe,deps1) ->
                   let deps2 =
                     let uu____8580 = FStar_List.unique (f :: deps1)  in
                     FStar_String.concat " " uu____8580  in
                   let wasm =
                     let uu____8589 =
                       FStar_Util.substring exe (Prims.parse_int "0")
                         ((FStar_String.length exe) - (Prims.parse_int "4"))
                        in
                     Prims.strcat uu____8589 ".wasm"  in
                   (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                    FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____8534);
         (let uu____8598 =
            let uu____8600 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8600 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____8598);
         (let uu____8619 =
            let uu____8621 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8621 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n" uu____8619);
         (let uu____8640 =
            let uu____8642 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8642 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____8640);
         (let uu____8660 =
            let uu____8662 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____8662 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____8660))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____8686 = FStar_Options.dep ()  in
    match uu____8686 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8698 ->
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
         fun uu____8753  ->
           fun s  ->
             match uu____8753 with
             | (v0,v1) ->
                 let uu____8782 =
                   let uu____8784 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   Prims.strcat "; " uu____8784  in
                 Prims.strcat s uu____8782) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8805 =
        let uu____8807 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8807  in
      has_interface deps.file_system_map uu____8805
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8823 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8823  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8834 =
                   let uu____8836 = module_name_of_file f  in
                   FStar_String.lowercase uu____8836  in
                 uu____8834 = m)))
  