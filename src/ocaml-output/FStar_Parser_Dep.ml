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
  fun uu___115_270  ->
    match uu___115_270 with
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
  fun uu___116_505  ->
    match uu___116_505 with
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
  dependence_graph -> Prims.string -> dep_node FStar_Pervasives_Native.option)
  =
  fun uu____746  ->
    fun k  -> match uu____746 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____768  ->
    fun k  ->
      fun v1  -> match uu____768 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____783  -> match uu____783 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____795  ->
    let uu____796 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____796
  
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
  let uu____845 = deps_empty ()  in
  let uu____846 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____845 uu____846 [] [] [] 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___117_867  ->
    match uu___117_867 with
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
      let uu____896 = FStar_Util.smap_try_find file_system_map key  in
      match uu____896 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____923) ->
          let uu____945 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____945
      | FStar_Pervasives_Native.Some
          (uu____948,FStar_Pervasives_Native.Some fn) ->
          let uu____971 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____971
      | uu____974 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1007 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1007 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1034) ->
          FStar_Pervasives_Native.Some iface
      | uu____1057 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1090 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1090 with
      | FStar_Pervasives_Native.Some
          (uu____1116,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1140 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1169 = interface_of file_system_map key  in
      FStar_Option.isSome uu____1169
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1189 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____1189
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____1203 =
      let uu____1205 = FStar_Options.lax ()  in
      if uu____1205
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____1203
  
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
                      (let uu____1262 = lowercase_module_name fn  in
                       key = uu____1262)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1281 = interface_of file_system_map key  in
              (match uu____1281 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1288 =
                     let uu____1294 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1294)  in
                   FStar_Errors.raise_err uu____1288
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1304 =
                (cmd_line_has_impl key) &&
                  (let uu____1307 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1307)
                 in
              if uu____1304
              then
                let uu____1314 = FStar_Options.expose_interfaces ()  in
                (if uu____1314
                 then
                   let uu____1318 =
                     let uu____1320 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____1320  in
                   maybe_add_suffix uu____1318
                 else
                   (let uu____1327 =
                      let uu____1333 =
                        let uu____1335 =
                          let uu____1337 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____1337  in
                        let uu____1342 =
                          let uu____1344 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____1344  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1335 uu____1342
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1333)
                       in
                    FStar_Errors.raise_err uu____1327))
              else
                (let uu____1354 =
                   let uu____1356 = interface_of file_system_map key  in
                   FStar_Option.get uu____1356  in
                 maybe_add_suffix uu____1354)
          | PreferInterface key ->
              let uu____1363 = implementation_of file_system_map key  in
              (match uu____1363 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1369 =
                     let uu____1375 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1375)
                      in
                   FStar_Errors.raise_err uu____1369
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____1385 = implementation_of file_system_map key  in
              (match uu____1385 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1391 =
                     let uu____1397 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1397)
                      in
                   FStar_Errors.raise_err uu____1391
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | FriendImplementation key ->
              let uu____1407 = implementation_of file_system_map key  in
              (match uu____1407 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1413 =
                     let uu____1419 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1419)
                      in
                   FStar_Errors.raise_err uu____1413
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
          let uu____1480 = deps_try_find deps fn  in
          match uu____1480 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____1488;_} ->
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
    (let uu____1502 =
       let uu____1504 =
         let uu____1506 =
           let uu____1508 =
             let uu____1512 =
               let uu____1516 = deps_keys graph  in
               FStar_List.unique uu____1516  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1530 =
                      let uu____1531 = deps_try_find graph k  in
                      FStar_Util.must uu____1531  in
                    uu____1530.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____1552 =
                      let uu____1554 = lowercase_module_name k  in
                      r uu____1554  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1552
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1512
              in
           FStar_String.concat "\n" uu____1508  in
         Prims.strcat uu____1506 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1504  in
     FStar_Util.write_file "dep.graph" uu____1502)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____1575  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1601 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1601  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1641 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1641
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1678 =
              let uu____1684 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1684)  in
            FStar_Errors.raise_err uu____1678)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1747 = FStar_Util.smap_try_find map1 key  in
      match uu____1747 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1794 = is_interface full_path  in
          if uu____1794
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1843 = is_interface full_path  in
          if uu____1843
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1885 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1903  ->
          match uu____1903 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1885);
    FStar_List.iter
      (fun f  ->
         let uu____1922 = lowercase_module_name f  in add_entry uu____1922 f)
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
        (let uu____1954 =
           let uu____1958 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1958  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1994 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1994  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1954);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2158 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2158 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2181 = string_of_lid l last1  in
      FStar_String.lowercase uu____2181
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2190 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2190
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2212 =
        let uu____2214 =
          let uu____2216 =
            let uu____2218 =
              let uu____2222 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2222  in
            FStar_Util.must uu____2218  in
          FStar_String.lowercase uu____2216  in
        uu____2214 <> k'  in
      if uu____2212
      then
        let uu____2227 = FStar_Ident.range_of_lid lid  in
        let uu____2228 =
          let uu____2234 =
            let uu____2236 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2236 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2234)  in
        FStar_Errors.log_issue uu____2227 uu____2228
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2252 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2274 = FStar_Options.prims_basename ()  in
      let uu____2276 =
        let uu____2280 = FStar_Options.pervasives_basename ()  in
        let uu____2282 =
          let uu____2286 = FStar_Options.pervasives_native_basename ()  in
          [uu____2286]  in
        uu____2280 :: uu____2282  in
      uu____2274 :: uu____2276  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2329 =
         let uu____2332 = lowercase_module_name full_filename  in
         namespace_of_module uu____2332  in
       match uu____2329 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2371 -> d = d'
  
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
      let set_interface_inlining uu____2436 =
        let uu____2437 = is_interface filename  in
        if uu____2437
        then FStar_ST.op_Colon_Equals has_inline_for_extraction true
        else ()  in
      let add_dep deps1 d =
        let uu____2644 =
          let uu____2646 =
            let uu____2648 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (dep_subsumed_by d) uu____2648  in
          Prims.op_Negation uu____2646  in
        if uu____2644
        then
          let uu____2717 =
            let uu____2720 = FStar_ST.op_Bang deps1  in d :: uu____2720  in
          FStar_ST.op_Colon_Equals deps1 uu____2717
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let dep_edge module_name = PreferInterface module_name  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2901 = resolve_module_name original_or_working_map key  in
        match uu____2901 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (dep_edge module_name);
             (let uu____2944 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____2944
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2983 -> false  in
      let record_open_module let_open lid =
        let uu____3002 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____3002
        then true
        else
          (if let_open
           then
             (let uu____3011 = FStar_Ident.range_of_lid lid  in
              let uu____3012 =
                let uu____3018 =
                  let uu____3020 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____3020  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3018)
                 in
              FStar_Errors.log_issue uu____3011 uu____3012)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____3040 = FStar_Ident.range_of_lid lid  in
          let uu____3041 =
            let uu____3047 =
              let uu____3049 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____3049
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____3047)
             in
          FStar_Errors.log_issue uu____3040 uu____3041
        else ()  in
      let record_open let_open lid =
        let uu____3069 = record_open_module let_open lid  in
        if uu____3069
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____3086 =
        match uu____3086 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____3093 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____3110 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____3110  in
        let alias = lowercase_join_longident lid true  in
        let uu____3115 = FStar_Util.smap_try_find original_map alias  in
        match uu____3115 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____3183 = FStar_Ident.range_of_lid lid  in
              let uu____3184 =
                let uu____3190 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3190)
                 in
              FStar_Errors.log_issue uu____3183 uu____3184);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____3201 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____3205 = add_dependence_edge working_map module_name  in
            if uu____3205
            then ()
            else
              (let uu____3210 = FStar_Options.debug_any ()  in
               if uu____3210
               then
                 let uu____3213 = FStar_Ident.range_of_lid lid  in
                 let uu____3214 =
                   let uu____3220 =
                     let uu____3222 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____3222
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____3220)
                    in
                 FStar_Errors.log_issue uu____3213 uu____3214
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___118_3352 =
         match uu___118_3352 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____3363 =
                   let uu____3365 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____3365  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____3371) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____3382 =
                   let uu____3384 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____3384  in
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
             let uu____3406 =
               let uu____3407 = lowercase_join_longident lid true  in
               FriendImplementation uu____3407  in
             add_dep deps uu____3406
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____3445 = record_module_alias ident lid  in
             if uu____3445
             then
               let uu____3448 =
                 let uu____3449 = lowercase_join_longident lid true  in
                 dep_edge uu____3449  in
               add_dep deps uu____3448
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____3487,patterms) ->
             FStar_List.iter
               (fun uu____3509  ->
                  match uu____3509 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____3518,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____3524,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3526;
               FStar_Parser_AST.mdest = uu____3527;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3529;
               FStar_Parser_AST.mdest = uu____3530;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____3532,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3534;
               FStar_Parser_AST.mdest = uu____3535;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____3539,tc,ts) ->
             (if tc then record_lid FStar_Parser_Const.mk_class_lid else ();
              (let ts1 =
                 FStar_List.map
                   (fun uu____3578  ->
                      match uu____3578 with | (x,docnik) -> x) ts
                  in
               FStar_List.iter collect_tycon ts1))
         | FStar_Parser_AST.Exception (uu____3591,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____3598 -> ()
         | FStar_Parser_AST.Pragma uu____3599 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____3635 =
                 let uu____3637 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____3637 > (Prims.parse_int "1")  in
               if uu____3635
               then
                 let uu____3684 =
                   let uu____3690 =
                     let uu____3692 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____3692
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____3690)  in
                 let uu____3697 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____3684 uu____3697
               else ()))
       
       and collect_tycon uu___119_3700 =
         match uu___119_3700 with
         | FStar_Parser_AST.TyconAbstract (uu____3701,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____3713,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____3727,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3773  ->
                   match uu____3773 with
                   | (uu____3782,t,uu____3784) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3789,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3851  ->
                   match uu____3851 with
                   | (uu____3865,t,uu____3867,uu____3868) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___120_3879 =
         match uu___120_3879 with
         | FStar_Parser_AST.DefineEffect (uu____3880,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3894,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder b =
         collect_aqual b.FStar_Parser_AST.aqual;
         (match b with
          | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3907,t);
              FStar_Parser_AST.brange = uu____3909;
              FStar_Parser_AST.blevel = uu____3910;
              FStar_Parser_AST.aqual = uu____3911;_} -> collect_term t
          | {
              FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3914,t);
              FStar_Parser_AST.brange = uu____3916;
              FStar_Parser_AST.blevel = uu____3917;
              FStar_Parser_AST.aqual = uu____3918;_} -> collect_term t
          | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
              FStar_Parser_AST.brange = uu____3922;
              FStar_Parser_AST.blevel = uu____3923;
              FStar_Parser_AST.aqual = uu____3924;_} -> collect_term t
          | uu____3927 -> ())
       
       and collect_aqual uu___121_3928 =
         match uu___121_3928 with
         | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
             collect_term t
         | uu____3932 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___122_3936 =
         match uu___122_3936 with
         | FStar_Const.Const_int
             (uu____3937,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3964 =
               let uu____3965 = FStar_Util.format2 "fstar.%sint%s" u w  in
               dep_edge uu____3965  in
             add_dep deps uu____3964
         | FStar_Const.Const_char uu____4001 ->
             add_dep deps (dep_edge "fstar.char")
         | FStar_Const.Const_float uu____4037 ->
             add_dep deps (dep_edge "fstar.float")
         | uu____4072 -> ()
       
       and collect_term' uu___124_4073 =
         match uu___124_4073 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____4082 =
                 let uu____4084 = FStar_Ident.text_of_id s  in
                 uu____4084 = "@"  in
               if uu____4082
               then
                 let uu____4089 =
                   let uu____4090 =
                     let uu____4091 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____4091
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____4090  in
                 collect_term' uu____4089
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____4095 -> ()
         | FStar_Parser_AST.Uvar uu____4096 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____4099) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____4133  ->
                   match uu____4133 with | (t,uu____4139) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____4149) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____4151,patterms,t) ->
             (FStar_List.iter
                (fun uu____4201  ->
                   match uu____4201 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____4230 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____4240,t1,t2) ->
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
                (fun uu____4336  ->
                   match uu____4336 with | (uu____4341,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____4344) -> collect_term t
         | FStar_Parser_AST.Product (binders,t) ->
             (collect_binders binders; collect_term t)
         | FStar_Parser_AST.Sum (binders,t) ->
             (FStar_List.iter
                (fun uu___123_4373  ->
                   match uu___123_4373 with
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
         | FStar_Parser_AST.NamedTyp (uu____4421,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____4425) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____4433) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____4441,uu____4442) ->
             collect_term t
         | FStar_Parser_AST.Quote (t,uu____4448) -> collect_term t
         | FStar_Parser_AST.Antiquote t -> collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___125_4458 =
         match uu___125_4458 with
         | FStar_Parser_AST.PatVar (uu____4459,aqual) -> collect_aqual aqual
         | FStar_Parser_AST.PatTvar (uu____4465,aqual) -> collect_aqual aqual
         | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
         | FStar_Parser_AST.PatOp uu____4474 -> ()
         | FStar_Parser_AST.PatConst uu____4475 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatName uu____4483 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____4491) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____4512  ->
                  match uu____4512 with | (uu____4517,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____4562 =
         match uu____4562 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____4580 = FStar_Parser_Driver.parse_file filename  in
       match uu____4580 with
       | (ast,uu____4604) ->
           let mname = lowercase_module_name filename  in
           ((let uu____4622 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____4622
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____4661 = FStar_ST.op_Bang deps  in
             let uu____4709 = FStar_ST.op_Bang mo_roots  in
             let uu____4757 = FStar_ST.op_Bang has_inline_for_extraction  in
             (uu____4661, uu____4709, uu____4757))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____4834 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____4834 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____4956 = dep_graph  in
    match uu____4956 with
    | Deps g -> let uu____4960 = FStar_Util.smap_copy g  in Deps uu____4960
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____5105 filename =
              match uu____5105 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____5146 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5146  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5177 = FStar_Options.debug_any ()  in
                         if uu____5177
                         then
                           let uu____5180 =
                             let uu____5182 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____5182  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5180
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___129_5193 = dep_node  in
                           { edges = (uu___129_5193.edges); color = Gray });
                        (let uu____5194 =
                           let uu____5205 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5205
                            in
                         match uu____5194 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___130_5241 = dep_node  in
                                 {
                                   edges = (uu___130_5241.edges);
                                   color = Black
                                 });
                              (let uu____5243 = FStar_Options.debug_any ()
                                  in
                               if uu____5243
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5249 =
                                 let uu____5253 =
                                   FStar_List.collect
                                     (fun uu___126_5260  ->
                                        match uu___126_5260 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____5253 all_friends1
                                  in
                               (uu____5249, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____5326 = FStar_Options.debug_any ()  in
             if uu____5326
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____5355 = deps  in
               match uu____5355 with
               | Deps dg ->
                   let uu____5359 = deps_empty ()  in
                   (match uu____5359 with
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
                                  | uu____5431 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____5439  ->
                                  let uu____5441 =
                                    let uu___131_5442 = dep_node  in
                                    let uu____5443 = widen_one dep_node.edges
                                       in
                                    { edges = uu____5443; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____5441)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____5445 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____5445
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____5450 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____5450 with
             | (friends,all_files_0) ->
                 ((let uu____5493 = FStar_Options.debug_any ()  in
                   if uu____5493
                   then
                     let uu____5496 =
                       let uu____5498 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____5498  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____5496
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____5517 =
                     (let uu____5529 = FStar_Options.debug_any ()  in
                      if uu____5529
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____5517 with
                   | (uu____5552,all_files) ->
                       ((let uu____5567 = FStar_Options.debug_any ()  in
                         if uu____5567
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____5574 = FStar_ST.op_Bang widened  in
                         (all_files, uu____5574))))))
  
let (collect : Prims.string Prims.list -> (Prims.string Prims.list * deps)) =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____5666 = FStar_Options.find_file fn  in
              match uu____5666 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5672 =
                    let uu____5678 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____5678)  in
                  FStar_Errors.raise_err uu____5672
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let interfaces_needing_inlining = FStar_Util.mk_ref []  in
    let add_interface_for_inlining l =
      let l1 = lowercase_module_name l  in
      let uu____5708 =
        let uu____5712 = FStar_ST.op_Bang interfaces_needing_inlining  in l1
          :: uu____5712
         in
      FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____5708  in
    let rec discover_one file_name =
      let uu____5819 =
        let uu____5821 = deps_try_find dep_graph file_name  in
        uu____5821 = FStar_Pervasives_Native.None  in
      if uu____5819
      then
        let uu____5827 =
          let uu____5839 =
            let uu____5853 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____5853 file_name  in
          match uu____5839 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____5827 with
        | (deps,mo_roots,needs_interface_inlining) ->
            (if needs_interface_inlining
             then add_interface_for_inlining file_name
             else ();
             (let deps1 =
                let module_name = lowercase_module_name file_name  in
                let uu____5990 =
                  (is_implementation file_name) &&
                    (has_interface file_system_map module_name)
                   in
                if uu____5990
                then FStar_List.append deps [UseInterface module_name]
                else deps  in
              let dep_node =
                let uu____5998 = FStar_List.unique deps1  in
                { edges = uu____5998; color = White }  in
              deps_add_dep dep_graph file_name dep_node;
              (let uu____6000 =
                 FStar_List.map
                   (file_of_dep file_system_map all_cmd_line_files1)
                   (FStar_List.append deps1 mo_roots)
                  in
               FStar_List.iter discover_one uu____6000)))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____6040 =
          let uu____6046 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____6046)  in
        FStar_Errors.raise_err uu____6040)
        in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy dep_graph  in
       let rec aux cycle filename =
         let node =
           let uu____6083 = deps_try_find dep_graph1 filename  in
           match uu____6083 with
           | FStar_Pervasives_Native.Some node -> node
           | FStar_Pervasives_Native.None  ->
               let uu____6087 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____6087
            in
         let direct_deps =
           FStar_All.pipe_right node.edges
             (FStar_List.collect
                (fun x  ->
                   match x with
                   | UseInterface f ->
                       let uu____6101 = implementation_of file_system_map f
                          in
                       (match uu____6101 with
                        | FStar_Pervasives_Native.None  -> [x]
                        | FStar_Pervasives_Native.Some fn when fn = filename
                            -> [x]
                        | uu____6112 -> [x; UseImplementation f])
                   | PreferInterface f ->
                       let uu____6118 = implementation_of file_system_map f
                          in
                       (match uu____6118 with
                        | FStar_Pervasives_Native.None  -> [x]
                        | FStar_Pervasives_Native.Some fn when fn = filename
                            -> [x]
                        | uu____6129 -> [x; UseImplementation f])
                   | uu____6133 -> [x]))
            in
         match node.color with
         | Gray  -> cycle_detected dep_graph1 cycle filename
         | Black  -> ()
         | White  ->
             (deps_add_dep dep_graph1 filename
                (let uu___132_6136 = node  in
                 { edges = direct_deps; color = Gray });
              (let uu____6138 =
                 dependences_of file_system_map dep_graph1
                   all_command_line_files filename
                  in
               FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6138);
              deps_add_dep dep_graph1 filename
                (let uu___133_6148 = node  in
                 { edges = direct_deps; color = Black }))
          in
       FStar_List.iter (aux []) all_command_line_files  in
     full_cycle_detection all_cmd_line_files1;
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining  in
      let uu____6214 =
        let uu____6223 =
          let uu____6225 = FStar_Options.codegen ()  in
          uu____6225 <> FStar_Pervasives_Native.None  in
        topological_dependences_of file_system_map dep_graph inlining_ifaces
          all_cmd_line_files1 uu____6223
         in
      match uu____6214 with
      | (all_files,uu____6238) ->
          ((let uu____6248 = FStar_Options.debug_any ()  in
            if uu____6248
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
          let uu____6315 = FStar_Options.find_file fn  in
          match uu____6315 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____6323 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____6337 = FStar_Options.debug_any ()  in
           if uu____6337
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____6356 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____6356
          then
            let uu____6367 =
              let uu____6374 =
                let uu____6376 =
                  let uu____6378 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____6378  in
                digest_of_file1 uu____6376  in
              ("interface", uu____6374)  in
            [uu____6367]
          else []  in
        let binary_deps =
          let uu____6410 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____6410
            (FStar_List.filter
               (fun fn2  ->
                  let uu____6425 =
                    (is_interface fn2) &&
                      (let uu____6428 = lowercase_module_name fn2  in
                       uu____6428 = module_name)
                     in
                  Prims.op_Negation uu____6425))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____6444 = lowercase_module_name fn11  in
                 let uu____6446 = lowercase_module_name fn2  in
                 FStar_String.compare uu____6444 uu____6446) binary_deps
           in
        let rec hash_deps out uu___127_6479 =
          match uu___127_6479 with
          | [] ->
              FStar_Pervasives_Native.Some
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let digest =
                let uu____6536 =
                  let uu____6540 =
                    let uu____6542 = cache_file_name fn2  in
                    FStar_Util.basename uu____6542  in
                  FStar_Options.find_file uu____6540  in
                match uu____6536 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some fn3 ->
                    let uu____6552 = digest_of_file1 fn3  in
                    FStar_Pervasives_Native.Some uu____6552
                 in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____6567 = FStar_Options.debug_any ()  in
                     if uu____6567
                     then
                       let uu____6570 =
                         let uu____6572 = cache_file_name fn2  in
                         FStar_Util.basename uu____6572  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____6570
                     else ());
                    FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some dig ->
                   let uu____6588 =
                     let uu____6597 =
                       let uu____6604 = lowercase_module_name fn2  in
                       (uu____6604, dig)  in
                     uu____6597 :: out  in
                   hash_deps uu____6588 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____6644 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____6670  ->
              match uu____6670 with
              | (m,d) ->
                  let uu____6684 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____6684))
       in
    FStar_All.pipe_right uu____6644 (FStar_String.concat "\n")
  
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
              let uu____6719 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____6719 FStar_Option.get  in
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
    let uu____6748 = deps.dep_graph  in
    match uu____6748 with
    | Deps deps1 ->
        let uu____6752 =
          let uu____6754 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____6772 =
                       let uu____6774 =
                         let uu____6776 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____6776
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____6774
                        in
                     uu____6772 :: out) []
             in
          FStar_All.pipe_right uu____6754 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____6752 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____6848 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____6848) ||
          (let uu____6855 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____6855)
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
            let uu____6898 =
              let uu____6902 = FStar_ST.op_Bang order  in ml_file ::
                uu____6902
               in
            FStar_ST.op_Colon_Equals order uu____6898
         in
      let rec aux uu___128_7009 =
        match uu___128_7009 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7037 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7037 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7040 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7040
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7044;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7053 = should_visit lc_module_name  in
              if uu____7053
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7061 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____7061);
                 (let uu____7066 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____7066);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7078 = FStar_ST.op_Bang order  in FStar_List.rev uu____7078)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7152 =
          let uu____7154 =
            let uu____7158 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7158  in
          FStar_Option.get uu____7154  in
        FStar_Util.replace_chars uu____7152 46 "_"  in
      FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7183 = output_file ".ml" f  in norm_path uu____7183  in
    let output_krml_file f =
      let uu____7195 = output_file ".krml" f  in norm_path uu____7195  in
    let output_cmx_file f =
      let uu____7207 = output_file ".cmx" f  in norm_path uu____7207  in
    let cache_file f =
      let uu____7219 = cache_file_name f  in norm_path uu____7219  in
    let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")  in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun file_name  ->
            let dep_node =
              let uu____7278 = deps_try_find deps.dep_graph file_name  in
              FStar_All.pipe_right uu____7278 FStar_Option.get  in
            let iface_deps =
              let uu____7288 = is_interface file_name  in
              if uu____7288
              then FStar_Pervasives_Native.None
              else
                (let uu____7299 =
                   let uu____7303 = lowercase_module_name file_name  in
                   interface_of deps.file_system_map uu____7303  in
                 match uu____7299 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some iface ->
                     let uu____7315 =
                       let uu____7318 =
                         let uu____7319 = deps_try_find deps.dep_graph iface
                            in
                         FStar_Option.get uu____7319  in
                       uu____7318.edges  in
                     FStar_Pervasives_Native.Some uu____7315)
               in
            let iface_deps1 =
              FStar_Util.map_opt iface_deps
                (FStar_List.filter
                   (fun iface_dep  ->
                      let uu____7336 =
                        FStar_Util.for_some (dep_subsumed_by iface_dep)
                          dep_node.edges
                         in
                      Prims.op_Negation uu____7336))
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
              FStar_List.map (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                files2
               in
            let files4 = FStar_String.concat "\\\n\t" files3  in
            (let uu____7396 = cache_file file_name  in
             FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7396 norm_f files4);
            (let already_there =
               let uu____7403 =
                 let uu____7417 =
                   let uu____7419 = output_file ".krml" file_name  in
                   norm_path uu____7419  in
                 FStar_Util.smap_try_find transitive_krml uu____7417  in
               match uu____7403 with
               | FStar_Pervasives_Native.Some
                   (uu____7436,already_there,uu____7438) -> already_there
               | FStar_Pervasives_Native.None  -> []  in
             (let uu____7473 =
                let uu____7475 = output_file ".krml" file_name  in
                norm_path uu____7475  in
              let uu____7478 =
                let uu____7490 =
                  let uu____7492 = output_file ".exe" file_name  in
                  norm_path uu____7492  in
                let uu____7495 =
                  let uu____7499 =
                    let uu____7503 =
                      let uu____7507 = deps_of deps file_name  in
                      FStar_List.map
                        (fun x  ->
                           let uu____7517 = output_file ".krml" x  in
                           norm_path uu____7517) uu____7507
                       in
                    FStar_List.append already_there uu____7503  in
                  FStar_List.unique uu____7499  in
                (uu____7490, uu____7495, false)  in
              FStar_Util.smap_add transitive_krml uu____7473 uu____7478);
             (let uu____7539 =
                let uu____7548 = FStar_Options.cmi ()  in
                if uu____7548
                then
                  topological_dependences_of deps.file_system_map
                    deps.dep_graph deps.interfaces_with_inlining [file_name]
                    true
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
                   let uu____7596 =
                     FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                       (FStar_List.append fst_files fst_files_from_iface)
                      in
                   (uu____7596, false))
                 in
              match uu____7539 with
              | (all_fst_files_dep,widened) ->
                  let all_checked_fst_files =
                    FStar_List.map cache_file all_fst_files_dep  in
                  let uu____7630 = is_implementation file_name  in
                  if uu____7630
                  then
                    ((let uu____7634 = (FStar_Options.cmi ()) && widened  in
                      if uu____7634
                      then
                        ((let uu____7638 = output_ml_file file_name  in
                          let uu____7640 = cache_file file_name  in
                          FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7638
                            uu____7640
                            (FStar_String.concat " \\\n\t"
                               all_checked_fst_files));
                         (let uu____7644 = output_krml_file file_name  in
                          let uu____7646 = cache_file file_name  in
                          FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7644
                            uu____7646
                            (FStar_String.concat " \\\n\t"
                               all_checked_fst_files)))
                      else
                        ((let uu____7653 = output_ml_file file_name  in
                          let uu____7655 = cache_file file_name  in
                          FStar_Util.print2 "%s: %s \n\n" uu____7653
                            uu____7655);
                         (let uu____7658 = output_krml_file file_name  in
                          let uu____7660 = cache_file file_name  in
                          FStar_Util.print2 "%s: %s\n\n" uu____7658
                            uu____7660)));
                     (let cmx_files =
                        let extracted_fst_files =
                          FStar_All.pipe_right all_fst_files_dep
                            (FStar_List.filter
                               (fun df  ->
                                  (let uu____7685 = lowercase_module_name df
                                      in
                                   let uu____7687 =
                                     lowercase_module_name file_name  in
                                   uu____7685 <> uu____7687) &&
                                    (let uu____7691 =
                                       lowercase_module_name df  in
                                     FStar_Options.should_extract uu____7691)))
                           in
                        FStar_All.pipe_right extracted_fst_files
                          (FStar_List.map output_cmx_file)
                         in
                      let uu____7701 =
                        let uu____7703 = lowercase_module_name file_name  in
                        FStar_Options.should_extract uu____7703  in
                      if uu____7701
                      then
                        let uu____7706 = output_cmx_file file_name  in
                        let uu____7708 = output_ml_file file_name  in
                        FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7706
                          uu____7708 (FStar_String.concat "\\\n\t" cmx_files)
                      else ()))
                  else
                    (let uu____7716 =
                       (let uu____7720 =
                          let uu____7722 = lowercase_module_name file_name
                             in
                          has_implementation deps.file_system_map uu____7722
                           in
                        Prims.op_Negation uu____7720) &&
                         (is_interface file_name)
                        in
                     if uu____7716
                     then
                       let uu____7725 = (FStar_Options.cmi ()) && widened  in
                       (if uu____7725
                        then
                          let uu____7728 = output_krml_file file_name  in
                          let uu____7730 = cache_file file_name  in
                          FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____7728
                            uu____7730
                            (FStar_String.concat " \\\n\t"
                               all_checked_fst_files)
                        else
                          (let uu____7736 = output_krml_file file_name  in
                           let uu____7738 = cache_file file_name  in
                           FStar_Util.print2 "%s: %s \n\n" uu____7736
                             uu____7738))
                     else ())))));
    (let all_fst_files =
       let uu____7747 =
         FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
       FStar_All.pipe_right uu____7747
         (FStar_Util.sort_with FStar_String.compare)
        in
     let all_ml_files =
       let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
       FStar_All.pipe_right all_fst_files
         (FStar_List.iter
            (fun fst_file  ->
               let mname = lowercase_module_name fst_file  in
               let uu____7788 = FStar_Options.should_extract mname  in
               if uu____7788
               then
                 let uu____7791 = output_ml_file fst_file  in
                 FStar_Util.smap_add ml_file_map mname uu____7791
               else ()));
       sort_output_files ml_file_map  in
     let all_krml_files =
       let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
       FStar_All.pipe_right keys
         (FStar_List.iter
            (fun fst_file  ->
               let mname = lowercase_module_name fst_file  in
               let uu____7818 = output_krml_file fst_file  in
               FStar_Util.smap_add krml_file_map mname uu____7818));
       sort_output_files krml_file_map  in
     let rec make_transitive f =
       let uu____7837 =
         let uu____7849 = FStar_Util.smap_try_find transitive_krml f  in
         FStar_Util.must uu____7849  in
       match uu____7837 with
       | (exe,deps1,seen) ->
           if seen
           then (exe, deps1)
           else
             (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
              (let deps2 =
                 let uu____7943 =
                   let uu____7947 =
                     FStar_List.map
                       (fun dep1  ->
                          let uu____7963 = make_transitive dep1  in
                          match uu____7963 with
                          | (uu____7975,deps2) -> dep1 :: deps2) deps1
                      in
                   FStar_List.flatten uu____7947  in
                 FStar_List.unique uu____7943  in
               FStar_Util.smap_add transitive_krml f (exe, deps2, true);
               (exe, deps2)))
        in
     (let uu____8011 = FStar_Util.smap_keys transitive_krml  in
      FStar_List.iter
        (fun f  ->
           let uu____8036 = make_transitive f  in
           match uu____8036 with
           | (exe,deps1) ->
               let deps2 =
                 let uu____8057 = FStar_List.unique (f :: deps1)  in
                 FStar_String.concat " " uu____8057  in
               let wasm =
                 let uu____8066 =
                   FStar_Util.substring exe (Prims.parse_int "0")
                     ((FStar_String.length exe) - (Prims.parse_int "4"))
                    in
                 Prims.strcat uu____8066 ".wasm"  in
               (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____8011);
     (let uu____8075 =
        let uu____8077 =
          FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)  in
        FStar_All.pipe_right uu____8077 (FStar_String.concat " \\\n\t")  in
      FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____8075);
     (let uu____8096 =
        let uu____8098 =
          FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)  in
        FStar_All.pipe_right uu____8098 (FStar_String.concat " \\\n\t")  in
      FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____8096);
     (let uu____8116 =
        let uu____8118 =
          FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)  in
        FStar_All.pipe_right uu____8118 (FStar_String.concat " \\\n\t")  in
      FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____8116))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____8142 = FStar_Options.dep ()  in
    match uu____8142 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8154 ->
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
         fun uu____8209  ->
           fun s  ->
             match uu____8209 with
             | (v0,v1) ->
                 let uu____8238 =
                   let uu____8240 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   Prims.strcat "; " uu____8240  in
                 Prims.strcat s uu____8238) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8261 =
        let uu____8263 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8263  in
      has_interface deps.file_system_map uu____8261
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8279 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8279  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8290 =
                   let uu____8292 = module_name_of_file f  in
                   FStar_String.lowercase uu____8292  in
                 uu____8290 = m)))
  