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
  fun uu___116_270  ->
    match uu___116_270 with
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
  fun uu___117_505  ->
    match uu___117_505 with
    | UseInterface f -> Prims.strcat "UseInterface " f
    | PreferInterface f -> Prims.strcat "PreferInterface " f
    | UseImplementation f -> Prims.strcat "UseImplementation " f
    | FriendImplementation f -> Prims.strcat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____524 . unit -> 'Auu____524 Prims.list =
  fun uu____527  -> [] 
type dependence_graph =
  | Deps of (dependences * color) FStar_Util.smap 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee  -> true 
let (__proj__Deps__item___0 :
  dependence_graph -> (dependences * color) FStar_Util.smap) =
  fun projectee  -> match projectee with | Deps _0 -> _0 
type deps =
  {
  dep_graph: dependence_graph ;
  file_system_map: files_for_module_name ;
  cmd_line_files: file_name Prims.list ;
  all_files: file_name Prims.list ;
  interfaces_with_inlining: module_name Prims.list }
let (__proj__Mkdeps__item__dep_graph : deps -> dependence_graph) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining;_} -> dep_graph
  
let (__proj__Mkdeps__item__file_system_map : deps -> files_for_module_name) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining;_} -> file_system_map
  
let (__proj__Mkdeps__item__cmd_line_files : deps -> file_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining;_} -> cmd_line_files
  
let (__proj__Mkdeps__item__all_files : deps -> file_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining;_} -> all_files
  
let (__proj__Mkdeps__item__interfaces_with_inlining :
  deps -> module_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining;_} -> interfaces_with_inlining
  
let (deps_try_find :
  dependence_graph ->
    Prims.string -> (dependences * color) FStar_Pervasives_Native.option)
  =
  fun uu____740  ->
    fun k  -> match uu____740 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph -> Prims.string -> (dependences * color) -> unit) =
  fun uu____778  ->
    fun k  ->
      fun v1  -> match uu____778 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____805  -> match uu____805 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____825  ->
    let uu____826 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____826
  
let (mk_deps :
  dependence_graph ->
    files_for_module_name ->
      file_name Prims.list ->
        file_name Prims.list -> module_name Prims.list -> deps)
  =
  fun dg  ->
    fun fs  ->
      fun c  ->
        fun a  ->
          fun i  ->
            {
              dep_graph = dg;
              file_system_map = fs;
              cmd_line_files = c;
              all_files = a;
              interfaces_with_inlining = i
            }
  
let (empty_deps : deps) =
  let uu____883 = deps_empty ()  in
  let uu____884 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____883 uu____884 [] [] [] 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___118_905  ->
    match uu___118_905 with
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
      let uu____934 = FStar_Util.smap_try_find file_system_map key  in
      match uu____934 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____961) ->
          let uu____983 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____983
      | FStar_Pervasives_Native.Some
          (uu____986,FStar_Pervasives_Native.Some fn) ->
          let uu____1009 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1009
      | uu____1012 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1045 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1045 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1072) ->
          FStar_Pervasives_Native.Some iface
      | uu____1095 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1128 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1128 with
      | FStar_Pervasives_Native.Some
          (uu____1154,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1178 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1207 = interface_of file_system_map key  in
      FStar_Option.isSome uu____1207
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1227 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____1227
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____1241 =
      let uu____1243 = FStar_Options.lax ()  in
      if uu____1243
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____1241
  
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
                      (let uu____1300 = lowercase_module_name fn  in
                       key = uu____1300)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1319 = interface_of file_system_map key  in
              (match uu____1319 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1326 =
                     let uu____1332 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1332)  in
                   FStar_Errors.raise_err uu____1326
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1342 =
                (cmd_line_has_impl key) &&
                  (let uu____1345 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1345)
                 in
              if uu____1342
              then
                let uu____1352 = FStar_Options.expose_interfaces ()  in
                (if uu____1352
                 then
                   let uu____1356 =
                     let uu____1358 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____1358  in
                   maybe_add_suffix uu____1356
                 else
                   (let uu____1365 =
                      let uu____1371 =
                        let uu____1373 =
                          let uu____1375 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____1375  in
                        let uu____1380 =
                          let uu____1382 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____1382  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1373 uu____1380
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1371)
                       in
                    FStar_Errors.raise_err uu____1365))
              else
                (let uu____1392 =
                   let uu____1394 = interface_of file_system_map key  in
                   FStar_Option.get uu____1394  in
                 maybe_add_suffix uu____1392)
          | PreferInterface key ->
              let uu____1401 = implementation_of file_system_map key  in
              (match uu____1401 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1407 =
                     let uu____1413 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1413)
                      in
                   FStar_Errors.raise_err uu____1407
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____1423 = implementation_of file_system_map key  in
              (match uu____1423 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1429 =
                     let uu____1435 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1435)
                      in
                   FStar_Errors.raise_err uu____1429
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | FriendImplementation key ->
              let uu____1445 = implementation_of file_system_map key  in
              (match uu____1445 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1451 =
                     let uu____1457 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1457)
                      in
                   FStar_Errors.raise_err uu____1451
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
  
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
          let uu____1518 = deps_try_find deps fn  in
          match uu____1518 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____1534) ->
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
    (let uu____1552 =
       let uu____1554 =
         let uu____1556 =
           let uu____1558 =
             let uu____1562 =
               let uu____1566 = deps_keys graph  in
               FStar_List.unique uu____1566  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1580 =
                      let uu____1585 = deps_try_find graph k  in
                      FStar_Util.must uu____1585  in
                    FStar_Pervasives_Native.fst uu____1580  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____1614 =
                      let uu____1616 = lowercase_module_name k  in
                      r uu____1616  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1614
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1562
              in
           FStar_String.concat "\n" uu____1558  in
         Prims.strcat uu____1556 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1554  in
     FStar_Util.write_file "dep.graph" uu____1552)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____1637  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1663 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1663  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1703 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1703
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1740 =
              let uu____1746 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1746)  in
            FStar_Errors.raise_err uu____1740)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1809 = FStar_Util.smap_try_find map1 key  in
      match uu____1809 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1856 = is_interface full_path  in
          if uu____1856
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1905 = is_interface full_path  in
          if uu____1905
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1947 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1965  ->
          match uu____1965 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1947);
    FStar_List.iter
      (fun f  ->
         let uu____1984 = lowercase_module_name f  in add_entry uu____1984 f)
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
        (let uu____2016 =
           let uu____2020 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2020  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2056 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2056  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2016);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2220 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2220 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2243 = string_of_lid l last1  in
      FStar_String.lowercase uu____2243
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2252 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2252
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2274 =
        let uu____2276 =
          let uu____2278 =
            let uu____2280 =
              let uu____2284 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2284  in
            FStar_Util.must uu____2280  in
          FStar_String.lowercase uu____2278  in
        uu____2276 <> k'  in
      if uu____2274
      then
        let uu____2289 = FStar_Ident.range_of_lid lid  in
        let uu____2290 =
          let uu____2296 =
            let uu____2298 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2298 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2296)  in
        FStar_Errors.log_issue uu____2289 uu____2290
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2314 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2336 = FStar_Options.prims_basename ()  in
      let uu____2338 =
        let uu____2342 = FStar_Options.pervasives_basename ()  in
        let uu____2344 =
          let uu____2348 = FStar_Options.pervasives_native_basename ()  in
          [uu____2348]  in
        uu____2342 :: uu____2344  in
      uu____2336 :: uu____2338  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2391 =
         let uu____2394 = lowercase_module_name full_filename  in
         namespace_of_module uu____2394  in
       match uu____2391 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2433 -> d = d'
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (dependence Prims.list * dependence Prims.list * Prims.bool))
  =
  fun original_map  ->
    fun filename  ->
      let deps = FStar_Util.mk_ref []  in
      let mo_roots = FStar_Util.mk_ref []  in
      let has_inline_for_extraction = FStar_Util.mk_ref false  in
      let set_interface_inlining uu____2498 =
        let uu____2499 = is_interface filename  in
        if uu____2499
        then FStar_ST.op_Colon_Equals has_inline_for_extraction true
        else ()  in
      let add_dep deps1 d =
        let uu____2706 =
          let uu____2708 =
            let uu____2710 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (dep_subsumed_by d) uu____2710  in
          Prims.op_Negation uu____2708  in
        if uu____2706
        then
          let uu____2779 =
            let uu____2782 = FStar_ST.op_Bang deps1  in d :: uu____2782  in
          FStar_ST.op_Colon_Equals deps1 uu____2779
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let dep_edge module_name = PreferInterface module_name  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2963 = resolve_module_name original_or_working_map key  in
        match uu____2963 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (dep_edge module_name);
             (let uu____3006 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____3006
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____3045 -> false  in
      let record_open_module let_open lid =
        let uu____3064 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____3064
        then true
        else
          (if let_open
           then
             (let uu____3073 = FStar_Ident.range_of_lid lid  in
              let uu____3074 =
                let uu____3080 =
                  let uu____3082 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____3082  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3080)
                 in
              FStar_Errors.log_issue uu____3073 uu____3074)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____3102 = FStar_Ident.range_of_lid lid  in
          let uu____3103 =
            let uu____3109 =
              let uu____3111 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____3111
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____3109)
             in
          FStar_Errors.log_issue uu____3102 uu____3103
        else ()  in
      let record_open let_open lid =
        let uu____3131 = record_open_module let_open lid  in
        if uu____3131
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____3148 =
        match uu____3148 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____3155 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____3172 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____3172  in
        let alias = lowercase_join_longident lid true  in
        let uu____3177 = FStar_Util.smap_try_find original_map alias  in
        match uu____3177 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____3245 = FStar_Ident.range_of_lid lid  in
              let uu____3246 =
                let uu____3252 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3252)
                 in
              FStar_Errors.log_issue uu____3245 uu____3246);
             false)
         in
      let add_dep_on_module module_name =
        let uu____3263 = add_dependence_edge working_map module_name  in
        if uu____3263
        then ()
        else
          (let uu____3268 = FStar_Options.debug_any ()  in
           if uu____3268
           then
             let uu____3271 = FStar_Ident.range_of_lid module_name  in
             let uu____3272 =
               let uu____3278 =
                 let uu____3280 = FStar_Ident.string_of_lid module_name  in
                 FStar_Util.format1 "Unbound module reference %s" uu____3280
                  in
               (FStar_Errors.Warning_UnboundModuleReference, uu____3278)  in
             FStar_Errors.log_issue uu____3271 uu____3272
           else ())
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____3292 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            add_dep_on_module module_name
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___119_3420 =
         match uu___119_3420 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____3431 =
                   let uu____3433 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____3433  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____3439) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____3450 =
                   let uu____3452 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____3452  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
              if
                FStar_List.contains FStar_Parser_AST.Inline_for_extraction
                  x.FStar_Parser_AST.quals
              then set_interface_inlining ()
              else ()) decls
       
       and collect_decl d =
         match d with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.Friend lid ->
             let uu____3474 =
               let uu____3475 = lowercase_join_longident lid true  in
               FriendImplementation uu____3475  in
             add_dep deps uu____3474
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____3513 = record_module_alias ident lid  in
             if uu____3513
             then
               let uu____3516 =
                 let uu____3517 = lowercase_join_longident lid true  in
                 dep_edge uu____3517  in
               add_dep deps uu____3516
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____3555,patterms) ->
             FStar_List.iter
               (fun uu____3577  ->
                  match uu____3577 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____3586,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____3592,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3594;
               FStar_Parser_AST.mdest = uu____3595;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3597;
               FStar_Parser_AST.mdest = uu____3598;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____3600,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3602;
               FStar_Parser_AST.mdest = uu____3603;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____3607,tc,ts) ->
             (if tc then record_lid FStar_Parser_Const.mk_class_lid else ();
              (let ts1 =
                 FStar_List.map
                   (fun uu____3646  ->
                      match uu____3646 with | (x,docnik) -> x) ts
                  in
               FStar_List.iter collect_tycon ts1))
         | FStar_Parser_AST.Exception (uu____3659,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____3666 -> ()
         | FStar_Parser_AST.Pragma uu____3667 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____3703 =
                 let uu____3705 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____3705 > (Prims.parse_int "1")  in
               if uu____3703
               then
                 let uu____3752 =
                   let uu____3758 =
                     let uu____3760 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____3760
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____3758)  in
                 let uu____3765 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____3752 uu____3765
               else ()))
       
       and collect_tycon uu___120_3768 =
         match uu___120_3768 with
         | FStar_Parser_AST.TyconAbstract (uu____3769,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____3781,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____3795,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3841  ->
                   match uu____3841 with
                   | (uu____3850,t,uu____3852) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3857,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3919  ->
                   match uu____3919 with
                   | (uu____3933,t,uu____3935,uu____3936) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___121_3947 =
         match uu___121_3947 with
         | FStar_Parser_AST.DefineEffect (uu____3948,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3962,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder b =
         collect_aqual b.FStar_Parser_AST.aqual;
         (match b with
          | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3975,t);
              FStar_Parser_AST.brange = uu____3977;
              FStar_Parser_AST.blevel = uu____3978;
              FStar_Parser_AST.aqual = uu____3979;_} -> collect_term t
          | {
              FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3982,t);
              FStar_Parser_AST.brange = uu____3984;
              FStar_Parser_AST.blevel = uu____3985;
              FStar_Parser_AST.aqual = uu____3986;_} -> collect_term t
          | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
              FStar_Parser_AST.brange = uu____3990;
              FStar_Parser_AST.blevel = uu____3991;
              FStar_Parser_AST.aqual = uu____3992;_} -> collect_term t
          | uu____3995 -> ())
       
       and collect_aqual uu___122_3996 =
         match uu___122_3996 with
         | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
             collect_term t
         | uu____4000 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___123_4004 =
         match uu___123_4004 with
         | FStar_Const.Const_int
             (uu____4005,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____4032 =
               let uu____4033 = FStar_Util.format2 "fstar.%sint%s" u w  in
               dep_edge uu____4033  in
             add_dep deps uu____4032
         | FStar_Const.Const_char uu____4069 ->
             add_dep deps (dep_edge "fstar.char")
         | FStar_Const.Const_float uu____4105 ->
             add_dep deps (dep_edge "fstar.float")
         | uu____4140 -> ()
       
       and collect_term' uu___126_4141 =
         match uu___126_4141 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____4150 =
                 let uu____4152 = FStar_Ident.text_of_id s  in
                 uu____4152 = "@"  in
               if uu____4150
               then
                 let uu____4157 =
                   let uu____4158 =
                     let uu____4159 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____4159
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____4158  in
                 collect_term' uu____4157
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____4163 -> ()
         | FStar_Parser_AST.Uvar uu____4164 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____4167) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____4201  ->
                   match uu____4201 with | (t,uu____4207) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____4217) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____4219,patterms,t) ->
             (FStar_List.iter
                (fun uu____4269  ->
                   match uu____4269 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____4298 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____4308,t1,t2) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Seq (t1,t2) -> (collect_term t1; collect_term t2)
         | FStar_Parser_AST.If (t1,t2,t3) ->
             (collect_term t1; collect_term t2; collect_term t3)
         | FStar_Parser_AST.Match (t,bs) ->
             (collect_term t; collect_branches bs)
         | FStar_Parser_AST.TryWith (t,bs) ->
             (collect_term t; collect_branches bs)
         | FStar_Parser_AST.Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Ascribed (t1,t2,FStar_Pervasives_Native.Some tac)
             -> (collect_term t1; collect_term t2; collect_term tac)
         | FStar_Parser_AST.Record (t,idterms) ->
             (FStar_Util.iter_opt t collect_term;
              FStar_List.iter
                (fun uu____4404  ->
                   match uu____4404 with | (uu____4409,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____4412) -> collect_term t
         | FStar_Parser_AST.Product (binders,t) ->
             (collect_binders binders; collect_term t)
         | FStar_Parser_AST.Sum (binders,t) ->
             (FStar_List.iter
                (fun uu___124_4441  ->
                   match uu___124_4441 with
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
         | FStar_Parser_AST.NamedTyp (uu____4489,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____4493) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____4501) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____4509,uu____4510) ->
             collect_term t
         | FStar_Parser_AST.Quote (t,uu____4516) -> collect_term t
         | FStar_Parser_AST.Antiquote t -> collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
         | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
             ((let uu____4530 = FStar_Ident.lid_of_str "FStar.Calc"  in
               add_dep_on_module uu____4530);
              collect_term rel;
              collect_term init1;
              FStar_List.iter
                (fun uu___125_4540  ->
                   match uu___125_4540 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       (collect_term rel1;
                        collect_term just;
                        collect_term next)) steps)
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___127_4550 =
         match uu___127_4550 with
         | FStar_Parser_AST.PatVar (uu____4551,aqual) -> collect_aqual aqual
         | FStar_Parser_AST.PatTvar (uu____4557,aqual) -> collect_aqual aqual
         | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
         | FStar_Parser_AST.PatOp uu____4566 -> ()
         | FStar_Parser_AST.PatConst uu____4567 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatName uu____4575 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____4583) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____4604  ->
                  match uu____4604 with | (uu____4609,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____4654 =
         match uu____4654 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____4672 = FStar_Parser_Driver.parse_file filename  in
       match uu____4672 with
       | (ast,uu____4696) ->
           let mname = lowercase_module_name filename  in
           ((let uu____4714 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____4714
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____4753 = FStar_ST.op_Bang deps  in
             let uu____4801 = FStar_ST.op_Bang mo_roots  in
             let uu____4849 = FStar_ST.op_Bang has_inline_for_extraction  in
             (uu____4753, uu____4801, uu____4849))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____4926 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____4926 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5048 = dep_graph  in
    match uu____5048 with
    | Deps g -> let uu____5056 = FStar_Util.smap_copy g  in Deps uu____5056
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____5209 filename =
              match uu____5209 with
              | (all_friends,all_files) ->
                  let uu____5249 =
                    let uu____5254 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5254  in
                  (match uu____5249 with
                   | (direct_deps,color) ->
                       (match color with
                        | Gray  ->
                            failwith
                              "Impossible: cycle detected after cycle detection has passed"
                        | Black  -> (all_friends, all_files)
                        | White  ->
                            ((let uu____5305 = FStar_Options.debug_any ()  in
                              if uu____5305
                              then
                                let uu____5308 =
                                  let uu____5310 =
                                    FStar_List.map dep_to_string direct_deps
                                     in
                                  FStar_String.concat ", " uu____5310  in
                                FStar_Util.print2
                                  "Visiting %s: direct deps are %s\n"
                                  filename uu____5308
                              else ());
                             deps_add_dep dep_graph1 filename
                               (direct_deps, Gray);
                             (let uu____5320 =
                                let uu____5331 =
                                  dependences_of file_system_map dep_graph1
                                    root_files filename
                                   in
                                all_friend_deps dep_graph1 cycle
                                  (all_friends, all_files) uu____5331
                                 in
                              match uu____5320 with
                              | (all_friends1,all_files1) ->
                                  (deps_add_dep dep_graph1 filename
                                     (direct_deps, Black);
                                   (let uu____5367 =
                                      FStar_Options.debug_any ()  in
                                    if uu____5367
                                    then
                                      FStar_Util.print1 "Adding %s\n"
                                        filename
                                    else ());
                                   (let uu____5373 =
                                      let uu____5377 =
                                        FStar_List.collect
                                          (fun uu___128_5384  ->
                                             match uu___128_5384 with
                                             | FriendImplementation m -> [m]
                                             | d -> []) direct_deps
                                         in
                                      FStar_List.append uu____5377
                                        all_friends1
                                       in
                                    (uu____5373, (filename :: all_files1))))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____5450 = FStar_Options.debug_any ()  in
             if uu____5450
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____5479 = deps  in
               match uu____5479 with
               | Deps dg ->
                   let uu____5487 = deps_empty ()  in
                   (match uu____5487 with
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
                                  | uu____5563 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun uu____5576  ->
                                fun uu____5577  ->
                                  match uu____5576 with
                                  | (dependences,color) ->
                                      let uu____5585 =
                                        let uu____5590 =
                                          widen_one dependences  in
                                        (uu____5590, White)  in
                                      FStar_Util.smap_add dg' filename
                                        uu____5585) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____5596 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____5596
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____5601 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____5601 with
             | (friends,all_files_0) ->
                 ((let uu____5644 = FStar_Options.debug_any ()  in
                   if uu____5644
                   then
                     let uu____5647 =
                       let uu____5649 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____5649  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____5647
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____5668 =
                     (let uu____5680 = FStar_Options.debug_any ()  in
                      if uu____5680
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____5668 with
                   | (uu____5703,all_files) ->
                       ((let uu____5718 = FStar_Options.debug_any ()  in
                         if uu____5718
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____5725 = FStar_ST.op_Bang widened  in
                         (all_files, uu____5725))))))
  
let (collect : Prims.string Prims.list -> (Prims.string Prims.list * deps)) =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____5817 = FStar_Options.find_file fn  in
              match uu____5817 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5823 =
                    let uu____5829 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____5829)  in
                  FStar_Errors.raise_err uu____5823
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let interfaces_needing_inlining = FStar_Util.mk_ref []  in
    let add_interface_for_inlining l =
      let l1 = lowercase_module_name l  in
      let uu____5859 =
        let uu____5863 = FStar_ST.op_Bang interfaces_needing_inlining  in l1
          :: uu____5863
         in
      FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____5859  in
    let rec discover_one file_name =
      let uu____5970 =
        let uu____5972 = deps_try_find dep_graph file_name  in
        uu____5972 = FStar_Pervasives_Native.None  in
      if uu____5970
      then
        let uu____5990 =
          let uu____6002 =
            let uu____6016 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____6016 file_name  in
          match uu____6002 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____5990 with
        | (deps,mo_roots,needs_interface_inlining) ->
            (if needs_interface_inlining
             then add_interface_for_inlining file_name
             else ();
             (let deps1 =
                let module_name = lowercase_module_name file_name  in
                let uu____6153 =
                  (is_implementation file_name) &&
                    (has_interface file_system_map module_name)
                   in
                if uu____6153
                then FStar_List.append deps [UseInterface module_name]
                else deps  in
              (let uu____6161 =
                 let uu____6166 = FStar_List.unique deps1  in
                 (uu____6166, White)  in
               deps_add_dep dep_graph file_name uu____6161);
              (let uu____6167 =
                 FStar_List.map
                   (file_of_dep file_system_map all_cmd_line_files1)
                   (FStar_List.append deps1 mo_roots)
                  in
               FStar_List.iter discover_one uu____6167)))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____6207 =
          let uu____6213 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____6213)  in
        FStar_Errors.raise_err uu____6207)
        in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy dep_graph  in
       let rec aux cycle filename =
         let uu____6249 =
           let uu____6256 = deps_try_find dep_graph1 filename  in
           match uu____6256 with
           | FStar_Pervasives_Native.Some (d,c) -> (d, c)
           | FStar_Pervasives_Native.None  ->
               let uu____6281 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____6281
            in
         match uu____6249 with
         | (direct_deps,color) ->
             let direct_deps1 =
               FStar_All.pipe_right direct_deps
                 (FStar_List.collect
                    (fun x  ->
                       match x with
                       | UseInterface f ->
                           let uu____6307 =
                             implementation_of file_system_map f  in
                           (match uu____6307 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____6318 -> [x; UseImplementation f])
                       | PreferInterface f ->
                           let uu____6324 =
                             implementation_of file_system_map f  in
                           (match uu____6324 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____6335 -> [x; UseImplementation f])
                       | uu____6339 -> [x]))
                in
             (match color with
              | Gray  -> cycle_detected dep_graph1 cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph1 filename (direct_deps1, Gray);
                   (let uu____6342 =
                      dependences_of file_system_map dep_graph1
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6342);
                   deps_add_dep dep_graph1 filename (direct_deps1, Black)))
          in
       FStar_List.iter (aux []) all_command_line_files  in
     full_cycle_detection all_cmd_line_files1;
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining  in
      let uu____6416 =
        let uu____6425 =
          let uu____6427 = FStar_Options.codegen ()  in
          uu____6427 <> FStar_Pervasives_Native.None  in
        topological_dependences_of file_system_map dep_graph inlining_ifaces
          all_cmd_line_files1 uu____6425
         in
      match uu____6416 with
      | (all_files,uu____6440) ->
          ((let uu____6450 = FStar_Options.debug_any ()  in
            if uu____6450
            then
              FStar_Util.print1 "Interfaces needing inlining: %s\n"
                (FStar_String.concat ", " inlining_ifaces)
            else ());
           (all_files,
             (mk_deps dep_graph file_system_map all_cmd_line_files1 all_files
                inlining_ifaces)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun deps  ->
    fun f  ->
      dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files
        f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string * Prims.string) Prims.list FStar_Pervasives_Native.option)
  =
  fun deps  ->
    fun fn  ->
      let file_system_map = deps.file_system_map  in
      let all_cmd_line_files = deps.cmd_line_files  in
      let deps1 = deps.dep_graph  in
      let fn1 =
        let uu____6510 = FStar_Options.find_file fn  in
        match uu____6510 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | uu____6518 -> fn  in
      let cache_file = cache_file_name fn1  in
      let digest_of_file1 fn2 =
        (let uu____6534 = FStar_Options.debug_any ()  in
         if uu____6534
         then FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
         else ());
        FStar_Util.digest_of_file fn2  in
      let module_name = lowercase_module_name fn1  in
      let source_hash = digest_of_file1 fn1  in
      let interface_hash =
        let uu____6553 =
          (is_implementation fn1) &&
            (has_interface file_system_map module_name)
           in
        if uu____6553
        then
          let uu____6564 =
            let uu____6571 =
              let uu____6573 =
                let uu____6575 = interface_of file_system_map module_name  in
                FStar_Option.get uu____6575  in
              digest_of_file1 uu____6573  in
            ("interface", uu____6571)  in
          [uu____6564]
        else []  in
      let binary_deps =
        let uu____6607 =
          dependences_of file_system_map deps1 all_cmd_line_files fn1  in
        FStar_All.pipe_right uu____6607
          (FStar_List.filter
             (fun fn2  ->
                let uu____6622 =
                  (is_interface fn2) &&
                    (let uu____6625 = lowercase_module_name fn2  in
                     uu____6625 = module_name)
                   in
                Prims.op_Negation uu____6622))
         in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11  ->
             fun fn2  ->
               let uu____6641 = lowercase_module_name fn11  in
               let uu____6643 = lowercase_module_name fn2  in
               FStar_String.compare uu____6641 uu____6643) binary_deps
         in
      let rec hash_deps out uu___129_6676 =
        match uu___129_6676 with
        | [] ->
            FStar_Pervasives_Native.Some
              (FStar_List.append (("source", source_hash) :: interface_hash)
                 out)
        | fn2::deps2 ->
            let digest =
              let fn3 = cache_file_name fn2  in
              if FStar_Util.file_exists fn3
              then
                let uu____6739 = digest_of_file1 fn3  in
                FStar_Pervasives_Native.Some uu____6739
              else
                (let uu____6744 =
                   let uu____6748 = FStar_Util.basename fn3  in
                   FStar_Options.find_file uu____6748  in
                 match uu____6744 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some fn4 ->
                     let uu____6758 = digest_of_file1 fn4  in
                     FStar_Pervasives_Native.Some uu____6758)
               in
            (match digest with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____6773 = FStar_Options.debug_any ()  in
                   if uu____6773
                   then
                     let uu____6776 = cache_file_name fn2  in
                     FStar_Util.print2 "%s: missed digest of file %s\n"
                       cache_file uu____6776
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some dig ->
                 let uu____6792 =
                   let uu____6801 =
                     let uu____6808 = lowercase_module_name fn2  in
                     (uu____6808, dig)  in
                   uu____6801 :: out  in
                 hash_deps uu____6792 deps2)
         in
      hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____6848 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____6874  ->
              match uu____6874 with
              | (m,d) ->
                  let uu____6888 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____6888))
       in
    FStar_All.pipe_right uu____6848 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun deps  ->
    let file_system_map = deps.file_system_map  in
    let all_cmd_line_files = deps.cmd_line_files  in
    let deps1 = deps.dep_graph  in
    let keys = deps_keys deps1  in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun f  ->
            let uu____6924 =
              let uu____6929 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____6929 FStar_Option.get  in
            match uu____6924 with
            | (f_deps,uu____6951) ->
                let files =
                  FStar_List.map
                    (file_of_dep file_system_map all_cmd_line_files) f_deps
                   in
                let files1 =
                  FStar_List.map
                    (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files
                   in
                FStar_Util.print2 "%s: %s\n\n" f
                  (FStar_String.concat " " files1)))
  
let (print_raw : deps -> unit) =
  fun deps  ->
    let uu____6976 = deps.dep_graph  in
    match uu____6976 with
    | Deps deps1 ->
        let uu____6984 =
          let uu____6986 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun uu____7004  ->
                   fun out  ->
                     match uu____7004 with
                     | (dep1,uu____7018) ->
                         let uu____7019 =
                           let uu____7021 =
                             let uu____7023 =
                               FStar_List.map dep_to_string dep1  in
                             FStar_All.pipe_right uu____7023
                               (FStar_String.concat ";\n\t")
                              in
                           FStar_Util.format2 "%s -> [\n\t%s\n] " k
                             uu____7021
                            in
                         uu____7019 :: out) []
             in
          FStar_All.pipe_right uu____6986 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____6984 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____7095 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7095) ||
          (let uu____7102 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7102)
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
            let uu____7145 =
              let uu____7149 = FStar_ST.op_Bang order  in ml_file ::
                uu____7149
               in
            FStar_ST.op_Colon_Equals order uu____7145
         in
      let rec aux uu___130_7256 =
        match uu___130_7256 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7284 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7284 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7295 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7295
                   | FStar_Pervasives_Native.Some (immediate_deps,uu____7299)
                       ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7312 = should_visit lc_module_name  in
              if uu____7312
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7320 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____7320);
                 (let uu____7325 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____7325);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7337 = FStar_ST.op_Bang order  in FStar_List.rev uu____7337)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7411 =
          let uu____7413 =
            let uu____7417 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7417  in
          FStar_Option.get uu____7413  in
        FStar_Util.replace_chars uu____7411 46 "_"  in
      FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7442 = output_file ".ml" f  in norm_path uu____7442  in
    let output_krml_file f =
      let uu____7454 = output_file ".krml" f  in norm_path uu____7454  in
    let output_cmx_file f =
      let uu____7466 = output_file ".cmx" f  in norm_path uu____7466  in
    let cache_file f =
      let uu____7478 = cache_file_name f  in norm_path uu____7478  in
    let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")  in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun file_name  ->
            let uu____7538 =
              let uu____7545 = deps_try_find deps.dep_graph file_name  in
              FStar_All.pipe_right uu____7545 FStar_Option.get  in
            match uu____7538 with
            | (f_deps,uu____7569) ->
                let iface_deps =
                  let uu____7579 = is_interface file_name  in
                  if uu____7579
                  then FStar_Pervasives_Native.None
                  else
                    (let uu____7590 =
                       let uu____7594 = lowercase_module_name file_name  in
                       interface_of deps.file_system_map uu____7594  in
                     match uu____7590 with
                     | FStar_Pervasives_Native.None  ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some iface ->
                         let uu____7606 =
                           let uu____7609 =
                             let uu____7614 =
                               deps_try_find deps.dep_graph iface  in
                             FStar_Option.get uu____7614  in
                           FStar_Pervasives_Native.fst uu____7609  in
                         FStar_Pervasives_Native.Some uu____7606)
                   in
                let iface_deps1 =
                  FStar_Util.map_opt iface_deps
                    (FStar_List.filter
                       (fun iface_dep  ->
                          let uu____7639 =
                            FStar_Util.for_some (dep_subsumed_by iface_dep)
                              f_deps
                             in
                          Prims.op_Negation uu____7639))
                   in
                let norm_f = norm_path file_name  in
                let files =
                  FStar_List.map
                    (file_of_dep_aux true deps.file_system_map
                       deps.cmd_line_files) f_deps
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
                ((let uu____7699 = cache_file file_name  in
                  FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7699 norm_f
                    files4);
                 (let already_there =
                    let uu____7706 =
                      let uu____7720 =
                        let uu____7722 = output_file ".krml" file_name  in
                        norm_path uu____7722  in
                      FStar_Util.smap_try_find transitive_krml uu____7720  in
                    match uu____7706 with
                    | FStar_Pervasives_Native.Some
                        (uu____7739,already_there,uu____7741) ->
                        already_there
                    | FStar_Pervasives_Native.None  -> []  in
                  (let uu____7776 =
                     let uu____7778 = output_file ".krml" file_name  in
                     norm_path uu____7778  in
                   let uu____7781 =
                     let uu____7793 =
                       let uu____7795 = output_file ".exe" file_name  in
                       norm_path uu____7795  in
                     let uu____7798 =
                       let uu____7802 =
                         let uu____7806 =
                           let uu____7810 = deps_of deps file_name  in
                           FStar_List.map
                             (fun x  ->
                                let uu____7820 = output_file ".krml" x  in
                                norm_path uu____7820) uu____7810
                            in
                         FStar_List.append already_there uu____7806  in
                       FStar_List.unique uu____7802  in
                     (uu____7793, uu____7798, false)  in
                   FStar_Util.smap_add transitive_krml uu____7776 uu____7781);
                  (let uu____7842 =
                     let uu____7851 = FStar_Options.cmi ()  in
                     if uu____7851
                     then
                       topological_dependences_of deps.file_system_map
                         deps.dep_graph deps.interfaces_with_inlining
                         [file_name] true
                     else
                       (let maybe_widen_deps f_deps1 =
                          FStar_List.map
                            (fun dep1  ->
                               file_of_dep_aux false deps.file_system_map
                                 deps.cmd_line_files dep1) f_deps1
                           in
                        let fst_files = maybe_widen_deps f_deps  in
                        let fst_files_from_iface =
                          match iface_deps1 with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some iface_deps2 ->
                              maybe_widen_deps iface_deps2
                           in
                        let uu____7899 =
                          FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                            (FStar_List.append fst_files fst_files_from_iface)
                           in
                        (uu____7899, false))
                      in
                   match uu____7842 with
                   | (all_fst_files_dep,widened) ->
                       let all_checked_fst_files =
                         FStar_List.map cache_file all_fst_files_dep  in
                       let uu____7933 = is_implementation file_name  in
                       if uu____7933
                       then
                         ((let uu____7937 = (FStar_Options.cmi ()) && widened
                              in
                           if uu____7937
                           then
                             ((let uu____7941 = output_ml_file file_name  in
                               let uu____7943 = cache_file file_name  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____7941 uu____7943
                                 (FStar_String.concat " \\\n\t"
                                    all_checked_fst_files));
                              (let uu____7947 = output_krml_file file_name
                                  in
                               let uu____7949 = cache_file file_name  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____7947 uu____7949
                                 (FStar_String.concat " \\\n\t"
                                    all_checked_fst_files)))
                           else
                             ((let uu____7956 = output_ml_file file_name  in
                               let uu____7958 = cache_file file_name  in
                               FStar_Util.print2 "%s: %s \n\n" uu____7956
                                 uu____7958);
                              (let uu____7961 = output_krml_file file_name
                                  in
                               let uu____7963 = cache_file file_name  in
                               FStar_Util.print2 "%s: %s\n\n" uu____7961
                                 uu____7963)));
                          (let cmx_files =
                             let extracted_fst_files =
                               FStar_All.pipe_right all_fst_files_dep
                                 (FStar_List.filter
                                    (fun df  ->
                                       (let uu____7988 =
                                          lowercase_module_name df  in
                                        let uu____7990 =
                                          lowercase_module_name file_name  in
                                        uu____7988 <> uu____7990) &&
                                         (let uu____7994 =
                                            lowercase_module_name df  in
                                          FStar_Options.should_extract
                                            uu____7994)))
                                in
                             FStar_All.pipe_right extracted_fst_files
                               (FStar_List.map output_cmx_file)
                              in
                           let uu____8004 =
                             let uu____8006 = lowercase_module_name file_name
                                in
                             FStar_Options.should_extract uu____8006  in
                           if uu____8004
                           then
                             let uu____8009 = output_cmx_file file_name  in
                             let uu____8011 = output_ml_file file_name  in
                             FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                               uu____8009 uu____8011
                               (FStar_String.concat "\\\n\t" cmx_files)
                           else ()))
                       else
                         (let uu____8019 =
                            (let uu____8023 =
                               let uu____8025 =
                                 lowercase_module_name file_name  in
                               has_implementation deps.file_system_map
                                 uu____8025
                                in
                             Prims.op_Negation uu____8023) &&
                              (is_interface file_name)
                             in
                          if uu____8019
                          then
                            let uu____8028 =
                              (FStar_Options.cmi ()) && widened  in
                            (if uu____8028
                             then
                               let uu____8031 = output_krml_file file_name
                                  in
                               let uu____8033 = cache_file file_name  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____8031 uu____8033
                                 (FStar_String.concat " \\\n\t"
                                    all_checked_fst_files)
                             else
                               (let uu____8039 = output_krml_file file_name
                                   in
                                let uu____8041 = cache_file file_name  in
                                FStar_Util.print2 "%s: %s \n\n" uu____8039
                                  uu____8041))
                          else ()))))));
    (let all_fst_files =
       let uu____8050 =
         FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
       FStar_All.pipe_right uu____8050
         (FStar_Util.sort_with FStar_String.compare)
        in
     let all_ml_files =
       let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
       FStar_All.pipe_right all_fst_files
         (FStar_List.iter
            (fun fst_file  ->
               let mname = lowercase_module_name fst_file  in
               let uu____8091 = FStar_Options.should_extract mname  in
               if uu____8091
               then
                 let uu____8094 = output_ml_file fst_file  in
                 FStar_Util.smap_add ml_file_map mname uu____8094
               else ()));
       sort_output_files ml_file_map  in
     let all_krml_files =
       let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
       FStar_All.pipe_right keys
         (FStar_List.iter
            (fun fst_file  ->
               let mname = lowercase_module_name fst_file  in
               let uu____8121 = output_krml_file fst_file  in
               FStar_Util.smap_add krml_file_map mname uu____8121));
       sort_output_files krml_file_map  in
     let rec make_transitive f =
       let uu____8140 =
         let uu____8152 = FStar_Util.smap_try_find transitive_krml f  in
         FStar_Util.must uu____8152  in
       match uu____8140 with
       | (exe,deps1,seen) ->
           if seen
           then (exe, deps1)
           else
             (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
              (let deps2 =
                 let uu____8246 =
                   let uu____8250 =
                     FStar_List.map
                       (fun dep1  ->
                          let uu____8266 = make_transitive dep1  in
                          match uu____8266 with
                          | (uu____8278,deps2) -> dep1 :: deps2) deps1
                      in
                   FStar_List.flatten uu____8250  in
                 FStar_List.unique uu____8246  in
               FStar_Util.smap_add transitive_krml f (exe, deps2, true);
               (exe, deps2)))
        in
     (let uu____8314 = FStar_Util.smap_keys transitive_krml  in
      FStar_List.iter
        (fun f  ->
           let uu____8339 = make_transitive f  in
           match uu____8339 with
           | (exe,deps1) ->
               let deps2 =
                 let uu____8360 = FStar_List.unique (f :: deps1)  in
                 FStar_String.concat " " uu____8360  in
               let wasm =
                 let uu____8369 =
                   FStar_Util.substring exe (Prims.parse_int "0")
                     ((FStar_String.length exe) - (Prims.parse_int "4"))
                    in
                 Prims.strcat uu____8369 ".wasm"  in
               (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____8314);
     (let uu____8378 =
        let uu____8380 =
          FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)  in
        FStar_All.pipe_right uu____8380 (FStar_String.concat " \\\n\t")  in
      FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____8378);
     (let uu____8399 =
        let uu____8401 =
          FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)  in
        FStar_All.pipe_right uu____8401 (FStar_String.concat " \\\n\t")  in
      FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____8399);
     (let uu____8419 =
        let uu____8421 =
          FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)  in
        FStar_All.pipe_right uu____8421 (FStar_String.concat " \\\n\t")  in
      FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____8419))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____8445 = FStar_Options.dep ()  in
    match uu____8445 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8457 ->
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
         fun uu____8512  ->
           fun s  ->
             match uu____8512 with
             | (v0,v1) ->
                 let uu____8541 =
                   let uu____8543 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   Prims.strcat "; " uu____8543  in
                 Prims.strcat s uu____8541) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8564 =
        let uu____8566 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8566  in
      has_interface deps.file_system_map uu____8564
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8582 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8582  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8593 =
                   let uu____8595 = module_name_of_file f  in
                   FStar_String.lowercase uu____8595  in
                 uu____8593 = m)))
  