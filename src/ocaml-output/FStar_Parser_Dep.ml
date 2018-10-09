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
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap
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
    ('Auu____279 FStar_Pervasives_Native.option,'Auu____279
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____279 Prims.list
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
    | FriendImplementation f -> Prims.strcat "UseImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____524 . unit -> 'Auu____524 Prims.list =
  fun uu____527  -> [] 
type dependence_graph =
  | Deps of (dependences,color) FStar_Pervasives_Native.tuple2
  FStar_Util.smap 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee  -> true 
let (__proj__Deps__item___0 :
  dependence_graph ->
    (dependences,color) FStar_Pervasives_Native.tuple2 FStar_Util.smap)
  = fun projectee  -> match projectee with | Deps _0 -> _0 
type deps =
  | Mk of
  (dependence_graph,files_for_module_name,file_name Prims.list,file_name
                                                                 Prims.list)
  FStar_Pervasives_Native.tuple4 
let (uu___is_Mk : deps -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk__item___0 :
  deps ->
    (dependence_graph,files_for_module_name,file_name Prims.list,file_name
                                                                   Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Mk _0 -> _0 
let (deps_try_find :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun uu____664  ->
    fun k  -> match uu____664 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun uu____702  ->
    fun k  ->
      fun v1  -> match uu____702 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____729  -> match uu____729 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____749  ->
    let uu____750 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____750
  
let (empty_deps : deps) =
  let uu____763 =
    let uu____778 = deps_empty ()  in
    let uu____779 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____778, uu____779, [], [])  in
  Mk uu____763 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___118_805  ->
    match uu___118_805 with
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
      let uu____834 = FStar_Util.smap_try_find file_system_map key  in
      match uu____834 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____861) ->
          let uu____883 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____883
      | FStar_Pervasives_Native.Some
          (uu____886,FStar_Pervasives_Native.Some fn) ->
          let uu____909 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____909
      | uu____912 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____945 = FStar_Util.smap_try_find file_system_map key  in
      match uu____945 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____972) ->
          FStar_Pervasives_Native.Some iface
      | uu____995 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1028 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1028 with
      | FStar_Pervasives_Native.Some
          (uu____1054,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1078 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1107 = interface_of file_system_map key  in
      FStar_Option.isSome uu____1107
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1127 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____1127
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____1141 =
      let uu____1143 = FStar_Options.lax ()  in
      if uu____1143
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____1141
  
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
                      (let uu____1200 = lowercase_module_name fn  in
                       key = uu____1200)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1219 = interface_of file_system_map key  in
              (match uu____1219 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1226 =
                     let uu____1232 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1232)  in
                   FStar_Errors.raise_err uu____1226
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1242 =
                (cmd_line_has_impl key) &&
                  (let uu____1245 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1245)
                 in
              if uu____1242
              then
                let uu____1252 = FStar_Options.expose_interfaces ()  in
                (if uu____1252
                 then
                   let uu____1256 =
                     let uu____1258 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____1258  in
                   maybe_add_suffix uu____1256
                 else
                   (let uu____1265 =
                      let uu____1271 =
                        let uu____1273 =
                          let uu____1275 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____1275  in
                        let uu____1280 =
                          let uu____1282 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____1282  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1273 uu____1280
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1271)
                       in
                    FStar_Errors.raise_err uu____1265))
              else
                (let uu____1292 =
                   let uu____1294 = interface_of file_system_map key  in
                   FStar_Option.get uu____1294  in
                 maybe_add_suffix uu____1292)
          | PreferInterface key ->
              let uu____1301 = implementation_of file_system_map key  in
              (match uu____1301 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1308 =
                     let uu____1314 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1314)
                      in
                   FStar_Errors.raise_err uu____1308
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____1324 = implementation_of file_system_map key  in
              (match uu____1324 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1331 =
                     let uu____1337 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1337)
                      in
                   FStar_Errors.raise_err uu____1331
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | FriendImplementation key ->
              let uu____1347 = implementation_of file_system_map key  in
              (match uu____1347 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1354 =
                     let uu____1360 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1360)
                      in
                   FStar_Errors.raise_err uu____1354
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
          let uu____1421 = deps_try_find deps fn  in
          match uu____1421 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____1437) ->
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
    (let uu____1455 =
       let uu____1457 =
         let uu____1459 =
           let uu____1461 =
             let uu____1465 =
               let uu____1469 = deps_keys graph  in
               FStar_List.unique uu____1469  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1483 =
                      let uu____1488 = deps_try_find graph k  in
                      FStar_Util.must uu____1488  in
                    FStar_Pervasives_Native.fst uu____1483  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1465
              in
           FStar_String.concat "\n" uu____1461  in
         Prims.strcat uu____1459 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1457  in
     FStar_Util.write_file "dep.graph" uu____1455)
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1536  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1562 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1562  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1602 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1602
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1639 =
              let uu____1645 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1645)  in
            FStar_Errors.raise_err uu____1639)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1708 = FStar_Util.smap_try_find map1 key  in
      match uu____1708 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1755 = is_interface full_path  in
          if uu____1755
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1804 = is_interface full_path  in
          if uu____1804
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1846 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1864  ->
          match uu____1864 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1846);
    FStar_List.iter
      (fun f  ->
         let uu____1883 = lowercase_module_name f  in add_entry uu____1883 f)
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
        (let uu____1915 =
           let uu____1919 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1919  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1955 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1955  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1915);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2119 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2119 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2142 = string_of_lid l last1  in
      FStar_String.lowercase uu____2142
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2151 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2151
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2173 =
        let uu____2175 =
          let uu____2177 =
            let uu____2179 =
              let uu____2183 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2183  in
            FStar_Util.must uu____2179  in
          FStar_String.lowercase uu____2177  in
        uu____2175 <> k'  in
      if uu____2173
      then
        let uu____2188 = FStar_Ident.range_of_lid lid  in
        let uu____2189 =
          let uu____2195 =
            let uu____2197 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2197 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2195)  in
        FStar_Errors.log_issue uu____2188 uu____2189
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2213 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2235 = FStar_Options.prims_basename ()  in
      let uu____2237 =
        let uu____2241 = FStar_Options.pervasives_basename ()  in
        let uu____2243 =
          let uu____2247 = FStar_Options.pervasives_native_basename ()  in
          [uu____2247]  in
        uu____2241 :: uu____2243  in
      uu____2235 :: uu____2237  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2290 =
         let uu____2293 = lowercase_module_name full_filename  in
         namespace_of_module uu____2293  in
       match uu____2290 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2332 -> d = d'
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (dependence Prims.list,dependence Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun original_map  ->
    fun filename  ->
      let deps = FStar_Util.mk_ref []  in
      let mo_roots = FStar_Util.mk_ref []  in
      let add_dep deps1 d =
        let uu____2538 =
          let uu____2540 =
            let uu____2542 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (dep_subsumed_by d) uu____2542  in
          Prims.op_Negation uu____2540  in
        if uu____2538
        then
          let uu____2611 =
            let uu____2614 = FStar_ST.op_Bang deps1  in d :: uu____2614  in
          FStar_ST.op_Colon_Equals deps1 uu____2611
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2787 = resolve_module_name original_or_working_map key  in
        match uu____2787 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2830 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____2830
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2869 -> false  in
      let record_open_module let_open lid =
        let uu____2888 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2888
        then true
        else
          (if let_open
           then
             (let uu____2897 = FStar_Ident.range_of_lid lid  in
              let uu____2898 =
                let uu____2904 =
                  let uu____2906 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2906  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2904)
                 in
              FStar_Errors.log_issue uu____2897 uu____2898)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2926 = FStar_Ident.range_of_lid lid  in
          let uu____2927 =
            let uu____2933 =
              let uu____2935 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2935
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2933)
             in
          FStar_Errors.log_issue uu____2926 uu____2927
        else ()  in
      let record_open let_open lid =
        let uu____2955 = record_open_module let_open lid  in
        if uu____2955
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2972 =
        match uu____2972 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2979 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2996 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2996  in
        let alias = lowercase_join_longident lid true  in
        let uu____3001 = FStar_Util.smap_try_find original_map alias  in
        match uu____3001 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____3069 = FStar_Ident.range_of_lid lid  in
              let uu____3070 =
                let uu____3076 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3076)
                 in
              FStar_Errors.log_issue uu____3069 uu____3070);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____3087 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____3091 = add_dependence_edge working_map module_name  in
            if uu____3091
            then ()
            else
              (let uu____3096 = FStar_Options.debug_any ()  in
               if uu____3096
               then
                 let uu____3099 = FStar_Ident.range_of_lid lid  in
                 let uu____3100 =
                   let uu____3106 =
                     let uu____3108 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____3108
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____3106)
                    in
                 FStar_Errors.log_issue uu____3099 uu____3100
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___119_3238 =
         match uu___119_3238 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____3249 =
                   let uu____3251 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____3251  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____3257) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____3268 =
                   let uu____3270 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____3270  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___120_3281 =
         match uu___120_3281 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.Friend lid ->
             let uu____3287 =
               let uu____3288 = lowercase_join_longident lid true  in
               FriendImplementation uu____3288  in
             add_dep deps uu____3287
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____3326 = record_module_alias ident lid  in
             if uu____3326
             then
               let uu____3329 =
                 let uu____3330 = lowercase_join_longident lid true  in
                 PreferInterface uu____3330  in
               add_dep deps uu____3329
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____3368,patterms) ->
             FStar_List.iter
               (fun uu____3390  ->
                  match uu____3390 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____3399,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____3405,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3407;
               FStar_Parser_AST.mdest = uu____3408;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3410;
               FStar_Parser_AST.mdest = uu____3411;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____3413,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____3415;
               FStar_Parser_AST.mdest = uu____3416;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____3420,tc,ts) ->
             (if tc then record_lid FStar_Parser_Const.mk_class_lid else ();
              (let ts1 =
                 FStar_List.map
                   (fun uu____3459  ->
                      match uu____3459 with | (x,docnik) -> x) ts
                  in
               FStar_List.iter collect_tycon ts1))
         | FStar_Parser_AST.Exception (uu____3472,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____3479 -> ()
         | FStar_Parser_AST.Pragma uu____3480 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____3516 =
                 let uu____3518 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____3518 > (Prims.parse_int "1")  in
               if uu____3516
               then
                 let uu____3565 =
                   let uu____3571 =
                     let uu____3573 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____3573
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____3571)  in
                 let uu____3578 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____3565 uu____3578
               else ()))
       
       and collect_tycon uu___121_3581 =
         match uu___121_3581 with
         | FStar_Parser_AST.TyconAbstract (uu____3582,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____3594,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____3608,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3654  ->
                   match uu____3654 with
                   | (uu____3663,t,uu____3665) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3670,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3732  ->
                   match uu____3732 with
                   | (uu____3746,t,uu____3748,uu____3749) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___122_3760 =
         match uu___122_3760 with
         | FStar_Parser_AST.DefineEffect (uu____3761,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3775,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder b =
         collect_aqual b.FStar_Parser_AST.aqual;
         (match b with
          | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3788,t);
              FStar_Parser_AST.brange = uu____3790;
              FStar_Parser_AST.blevel = uu____3791;
              FStar_Parser_AST.aqual = uu____3792;_} -> collect_term t
          | {
              FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3795,t);
              FStar_Parser_AST.brange = uu____3797;
              FStar_Parser_AST.blevel = uu____3798;
              FStar_Parser_AST.aqual = uu____3799;_} -> collect_term t
          | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
              FStar_Parser_AST.brange = uu____3803;
              FStar_Parser_AST.blevel = uu____3804;
              FStar_Parser_AST.aqual = uu____3805;_} -> collect_term t
          | uu____3808 -> ())
       
       and collect_aqual uu___123_3809 =
         match uu___123_3809 with
         | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
             collect_term t
         | uu____3813 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___124_3817 =
         match uu___124_3817 with
         | FStar_Const.Const_int
             (uu____3818,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3845 =
               let uu____3846 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____3846  in
             add_dep deps uu____3845
         | FStar_Const.Const_char uu____3882 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3918 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3953 -> ()
       
       and collect_term' uu___126_3954 =
         match uu___126_3954 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____3963 =
                 let uu____3965 = FStar_Ident.text_of_id s  in
                 uu____3965 = "@"  in
               if uu____3963
               then
                 let uu____3970 =
                   let uu____3971 =
                     let uu____3972 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____3972
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3971  in
                 collect_term' uu____3970
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3976 -> ()
         | FStar_Parser_AST.Uvar uu____3977 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3980) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____4014  ->
                   match uu____4014 with | (t,uu____4020) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____4030) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____4032,patterms,t) ->
             (FStar_List.iter
                (fun uu____4082  ->
                   match uu____4082 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____4111 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____4121,t1,t2) ->
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
                (fun uu____4217  ->
                   match uu____4217 with | (uu____4222,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____4225) -> collect_term t
         | FStar_Parser_AST.Product (binders,t) ->
             (collect_binders binders; collect_term t)
         | FStar_Parser_AST.Sum (binders,t) ->
             (FStar_List.iter
                (fun uu___125_4254  ->
                   match uu___125_4254 with
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
         | FStar_Parser_AST.NamedTyp (uu____4302,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____4306) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____4314) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____4322,uu____4323) ->
             collect_term t
         | FStar_Parser_AST.Quote (t,uu____4329) -> collect_term t
         | FStar_Parser_AST.Antiquote t -> collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___127_4339 =
         match uu___127_4339 with
         | FStar_Parser_AST.PatVar (uu____4340,aqual) -> collect_aqual aqual
         | FStar_Parser_AST.PatTvar (uu____4346,aqual) -> collect_aqual aqual
         | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
         | FStar_Parser_AST.PatOp uu____4355 -> ()
         | FStar_Parser_AST.PatConst uu____4356 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatName uu____4364 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____4372) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____4393  ->
                  match uu____4393 with | (uu____4398,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____4443 =
         match uu____4443 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____4461 = FStar_Parser_Driver.parse_file filename  in
       match uu____4461 with
       | (ast,uu____4482) ->
           let mname = lowercase_module_name filename  in
           ((let uu____4500 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____4500
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____4539 = FStar_ST.op_Bang deps  in
             let uu____4587 = FStar_ST.op_Bang mo_roots  in
             (uu____4539, uu____4587))))
  
let (collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap FStar_ST.ref)
  =
  let uu____4663 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____4663 
let (set_collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____4801 = FStar_Options.find_file fn  in
              match uu____4801 with
              | FStar_Pervasives_Native.None  ->
                  let uu____4807 =
                    let uu____4813 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____4813)  in
                  FStar_Errors.raise_err uu____4807
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____4831 =
        let uu____4833 = deps_try_find dep_graph file_name  in
        uu____4833 = FStar_Pervasives_Native.None  in
      if uu____4831
      then
        let uu____4851 =
          let uu____4860 =
            let uu____4871 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____4871 file_name  in
          match uu____4860 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____4851 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____4977 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____4977
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____4985 =
                let uu____4990 = FStar_List.unique deps1  in
                (uu____4990, White)  in
              deps_add_dep dep_graph file_name uu____4985);
             (let uu____4991 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____4991))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let dep_graph_copy dep_graph1 =
       let uu____5007 = dep_graph1  in
       match uu____5007 with
       | Deps g ->
           let uu____5015 = FStar_Util.smap_copy g  in Deps uu____5015
        in
     let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____5056 =
          let uu____5062 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____5062)  in
        FStar_Errors.raise_err uu____5056)
        in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy dep_graph  in
       let rec aux cycle filename =
         let uu____5098 =
           let uu____5105 = deps_try_find dep_graph1 filename  in
           match uu____5105 with
           | FStar_Pervasives_Native.Some (d,c) -> (d, c)
           | FStar_Pervasives_Native.None  ->
               let uu____5130 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____5130
            in
         match uu____5098 with
         | (direct_deps,color) ->
             let direct_deps1 =
               FStar_All.pipe_right direct_deps
                 (FStar_List.collect
                    (fun x  ->
                       match x with
                       | UseInterface f ->
                           let uu____5156 =
                             implementation_of file_system_map f  in
                           (match uu____5156 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____5167 -> [x; UseImplementation f])
                       | PreferInterface f ->
                           let uu____5173 =
                             implementation_of file_system_map f  in
                           (match uu____5173 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____5184 -> [x; UseImplementation f])
                       | uu____5188 -> [x]))
                in
             (match color with
              | Gray  -> cycle_detected dep_graph1 cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph1 filename (direct_deps1, Gray);
                   (let uu____5191 =
                      dependences_of file_system_map dep_graph1
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____5191);
                   deps_add_dep dep_graph1 filename (direct_deps1, Black)))
          in
       FStar_List.iter (aux []) all_command_line_files  in
     full_cycle_detection all_cmd_line_files1;
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let topological_dependences_of all_command_line_files =
        let rec all_friend_deps_1 dep_graph1 cycle uu____5311 filename =
          match uu____5311 with
          | (all_friends,all_files) ->
              let uu____5347 =
                let uu____5352 = deps_try_find dep_graph1 filename  in
                FStar_Util.must uu____5352  in
              (match uu____5347 with
               | (direct_deps,color) ->
                   (match color with
                    | Gray  ->
                        (cycle_detected dep_graph1 cycle filename;
                         (all_friends, all_files))
                    | Black  -> (all_friends, all_files)
                    | White  ->
                        (deps_add_dep dep_graph1 filename (direct_deps, Gray);
                         (let uu____5395 =
                            let uu____5405 =
                              dependences_of file_system_map dep_graph1
                                all_command_line_files filename
                               in
                            all_friend_deps dep_graph1 cycle
                              (all_friends, all_files) uu____5405
                             in
                          match uu____5395 with
                          | (all_friends1,all_files1) ->
                              (deps_add_dep dep_graph1 filename
                                 (direct_deps, Black);
                               (let uu____5436 =
                                  let uu____5439 =
                                    FStar_List.filter
                                      (fun uu___128_5444  ->
                                         match uu___128_5444 with
                                         | FriendImplementation uu____5446 ->
                                             true
                                         | uu____5449 -> false) direct_deps
                                     in
                                  FStar_List.append uu____5439 all_friends1
                                   in
                                (uu____5436, (filename :: all_files1))))))))
        
        and all_friend_deps dep_graph1 cycle all_friends filenames =
          FStar_List.fold_left
            (fun all_friends1  ->
               fun k  ->
                 all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
            all_friends filenames
         in
        let uu____5501 =
          let uu____5511 = dep_graph_copy dep_graph  in
          all_friend_deps uu____5511 [] ([], []) all_command_line_files  in
        match uu____5501 with
        | (friends,uu____5523) ->
            let widen_deps friends1 deps =
              FStar_All.pipe_right deps
                (FStar_List.map
                   (fun d  ->
                      match d with
                      | PreferInterface f when
                          FStar_List.contains (FriendImplementation f)
                            friends1
                          -> FriendImplementation f
                      | uu____5564 -> d))
               in
            let uu____5565 =
              let uu____5575 = dep_graph  in
              match uu____5575 with
              | Deps dg ->
                  let uu____5592 = deps_empty ()  in
                  (match uu____5592 with
                   | Deps dg' ->
                       (FStar_Util.smap_fold dg
                          (fun filename  ->
                             fun uu____5621  ->
                               fun uu____5622  ->
                                 match uu____5621 with
                                 | (dependences,color) ->
                                     let uu____5630 =
                                       let uu____5635 =
                                         widen_deps friends dependences  in
                                       (uu____5635, color)  in
                                     FStar_Util.smap_add dg' filename
                                       uu____5630) ();
                        all_friend_deps (Deps dg') [] ([], [])
                          all_command_line_files))
               in
            (match uu____5565 with | (uu____5650,all_files) -> all_files)
         in
      let all_files = topological_dependences_of all_cmd_line_files1  in
      (all_files,
        (Mk (dep_graph, file_system_map, all_cmd_line_files1, all_files)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____5688  ->
    fun f  ->
      match uu____5688 with
      | Mk (deps,file_system_map,all_cmd_line_files,uu____5697) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____5733  ->
    fun fn  ->
      match uu____5733 with
      | Mk (deps,file_system_map,all_cmd_line_files,uu____5749) ->
          let fn1 =
            let uu____5764 = FStar_Options.find_file fn  in
            match uu____5764 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____5772 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____5788 = FStar_Options.debug_any ()  in
             if uu____5788
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____5807 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____5807
            then
              let uu____5818 =
                let uu____5825 =
                  let uu____5827 =
                    let uu____5829 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____5829  in
                  digest_of_file1 uu____5827  in
                ("interface", uu____5825)  in
              [uu____5818]
            else []  in
          let binary_deps =
            let uu____5861 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____5861
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____5876 =
                      (is_interface fn2) &&
                        (let uu____5879 = lowercase_module_name fn2  in
                         uu____5879 = module_name)
                       in
                    Prims.op_Negation uu____5876))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____5895 = lowercase_module_name fn11  in
                   let uu____5897 = lowercase_module_name fn2  in
                   FStar_String.compare uu____5895 uu____5897) binary_deps
             in
          let rec hash_deps out uu___129_5930 =
            match uu___129_5930 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let digest =
                  let fn3 = cache_file_name fn2  in
                  if FStar_Util.file_exists fn3
                  then
                    let uu____5993 = digest_of_file1 fn3  in
                    FStar_Pervasives_Native.Some uu____5993
                  else
                    (let uu____5998 =
                       let uu____6002 = FStar_Util.basename fn3  in
                       FStar_Options.find_file uu____6002  in
                     match uu____5998 with
                     | FStar_Pervasives_Native.None  ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some fn4 ->
                         let uu____6012 = digest_of_file1 fn4  in
                         FStar_Pervasives_Native.Some uu____6012)
                   in
                (match digest with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6027 = FStar_Options.debug_any ()  in
                       if uu____6027
                       then
                         let uu____6030 = cache_file_name fn2  in
                         FStar_Util.print2 "%s: missed digest of file %s\n"
                           cache_file uu____6030
                       else ());
                      FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.Some dig ->
                     let uu____6046 =
                       let uu____6055 =
                         let uu____6062 = lowercase_module_name fn2  in
                         (uu____6062, dig)  in
                       uu____6055 :: out  in
                     hash_deps uu____6046 deps1)
             in
          hash_deps [] binary_deps1
  
let (print_digest :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string)
  =
  fun dig  ->
    let uu____6102 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____6128  ->
              match uu____6128 with
              | (m,d) ->
                  let uu____6142 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____6142))
       in
    FStar_All.pipe_right uu____6102 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____6155  ->
    match uu____6155 with
    | Mk (deps,file_system_map,all_cmd_line_files,uu____6159) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____6188 =
                  let uu____6193 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____6193 FStar_Option.get  in
                match uu____6188 with
                | (f_deps,uu____6215) ->
                    let files =
                      FStar_List.map
                        (file_of_dep file_system_map all_cmd_line_files)
                        f_deps
                       in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files
                       in
                    FStar_Util.print2 "%s: %s\n\n" f
                      (FStar_String.concat " " files1)))
  
let (print_raw : deps -> unit) =
  fun deps  ->
    let uu____6240 = deps  in
    match uu____6240 with
    | Mk (Deps deps1,uu____6242,uu____6243,uu____6244) ->
        let uu____6263 =
          let uu____6265 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun uu____6283  ->
                   fun out  ->
                     match uu____6283 with
                     | (dep1,uu____6297) ->
                         let uu____6298 =
                           let uu____6300 =
                             let uu____6302 =
                               FStar_List.map dep_to_string dep1  in
                             FStar_All.pipe_right uu____6302
                               (FStar_String.concat ";\n\t")
                              in
                           FStar_Util.format2 "%s -> [\n\t%s\n] " k
                             uu____6300
                            in
                         uu____6298 :: out) []
             in
          FStar_All.pipe_right uu____6265 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____6263 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let uu____6327 = deps  in
    match uu____6327 with
    | Mk (deps1,file_system_map,all_cmd_line_files,all_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____6391 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____6391) ||
              (let uu____6398 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____6398)
             in
          let mark_visiting lc_module_name =
            let ml_file_opt =
              FStar_Util.smap_try_find remaining_output_files lc_module_name
               in
            FStar_Util.smap_remove remaining_output_files lc_module_name;
            FStar_Util.smap_add visited_other_modules lc_module_name true;
            ml_file_opt  in
          let emit_output_file_opt ml_file_opt =
            match ml_file_opt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some ml_file ->
                let uu____6441 =
                  let uu____6445 = FStar_ST.op_Bang order  in ml_file ::
                    uu____6445
                   in
                FStar_ST.op_Colon_Equals order uu____6441
             in
          let rec aux uu___130_6552 =
            match uu___130_6552 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____6580 = deps_try_find deps1 file_name  in
                      (match uu____6580 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____6591 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____6591
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____6595) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____6608 = should_visit lc_module_name  in
                  if uu____6608
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____6616 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____6616);
                     (let uu____6621 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____6621);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____6633 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____6633)
           in
        let keys = deps_keys deps1  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____6707 =
              let uu____6709 =
                let uu____6713 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____6713  in
              FStar_Option.get uu____6709  in
            FStar_Util.replace_chars uu____6707 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____6738 = output_file ".ml" f  in norm_path uu____6738  in
        let output_krml_file f =
          let uu____6750 = output_file ".krml" f  in norm_path uu____6750  in
        let output_cmx_file f =
          let uu____6762 = output_file ".cmx" f  in norm_path uu____6762  in
        let cache_file f =
          let uu____6774 = cache_file_name f  in norm_path uu____6774  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____6830 =
                   let uu____6837 = deps_try_find deps1 f  in
                   FStar_All.pipe_right uu____6837 FStar_Option.get  in
                 match uu____6830 with
                 | (f_deps,uu____6861) ->
                     let iface_deps =
                       let uu____6871 = is_interface f  in
                       if uu____6871
                       then FStar_Pervasives_Native.None
                       else
                         (let uu____6882 =
                            let uu____6886 = lowercase_module_name f  in
                            interface_of file_system_map uu____6886  in
                          match uu____6882 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some iface ->
                              let uu____6898 =
                                let uu____6901 =
                                  let uu____6906 = deps_try_find deps1 iface
                                     in
                                  FStar_Option.get uu____6906  in
                                FStar_Pervasives_Native.fst uu____6901  in
                              FStar_Pervasives_Native.Some uu____6898)
                        in
                     let iface_deps1 =
                       FStar_Util.map_opt iface_deps
                         (FStar_List.filter
                            (fun iface_dep  ->
                               let uu____6931 =
                                 FStar_Util.for_some
                                   (dep_subsumed_by iface_dep) f_deps
                                  in
                               Prims.op_Negation uu____6931))
                        in
                     let norm_f = norm_path f  in
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps
                        in
                     let files1 =
                       match iface_deps1 with
                       | FStar_Pervasives_Native.None  -> files
                       | FStar_Pervasives_Native.Some iface_deps2 ->
                           let iface_files =
                             FStar_List.map
                               (file_of_dep_aux true file_system_map
                                  all_cmd_line_files) iface_deps2
                              in
                           FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                             (FStar_List.append files iface_files)
                        in
                     let files2 = FStar_List.map norm_path files1  in
                     let files3 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files2
                        in
                     let files4 = FStar_String.concat "\\\n\t" files3  in
                     ((let uu____6991 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____6991
                         norm_f files4);
                      (let already_there =
                         let uu____6998 =
                           let uu____7012 =
                             let uu____7014 = output_file ".krml" f  in
                             norm_path uu____7014  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____7012
                            in
                         match uu____6998 with
                         | FStar_Pervasives_Native.Some
                             (uu____7031,already_there,uu____7033) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____7068 =
                          let uu____7070 = output_file ".krml" f  in
                          norm_path uu____7070  in
                        let uu____7073 =
                          let uu____7085 =
                            let uu____7087 = output_file ".exe" f  in
                            norm_path uu____7087  in
                          let uu____7090 =
                            let uu____7094 =
                              let uu____7098 =
                                let uu____7102 =
                                  deps_of
                                    (Mk
                                       (deps1, file_system_map,
                                         all_cmd_line_files, all_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____7118 = output_file ".krml" x
                                        in
                                     norm_path uu____7118) uu____7102
                                 in
                              FStar_List.append already_there uu____7098  in
                            FStar_List.unique uu____7094  in
                          (uu____7085, uu____7090, false)  in
                        FStar_Util.smap_add transitive_krml uu____7068
                          uu____7073);
                       (let uu____7140 = is_implementation f  in
                        if uu____7140
                        then
                          ((let uu____7144 = output_ml_file f  in
                            let uu____7146 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____7144
                              uu____7146);
                           (let cmx_files =
                              let fst_files =
                                FStar_All.pipe_right f_deps
                                  (FStar_List.map
                                     (file_of_dep_aux false file_system_map
                                        all_cmd_line_files))
                                 in
                              let fst_files_from_iface =
                                match iface_deps1 with
                                | FStar_Pervasives_Native.None  -> []
                                | FStar_Pervasives_Native.Some iface_deps2 ->
                                    let id1 =
                                      FStar_All.pipe_right iface_deps2
                                        (FStar_List.map
                                           (file_of_dep_aux false
                                              file_system_map
                                              all_cmd_line_files))
                                       in
                                    id1
                                 in
                              let fst_files1 =
                                FStar_Util.remove_dups
                                  (fun x  -> fun y  -> x = y)
                                  (FStar_List.append fst_files
                                     fst_files_from_iface)
                                 in
                              let extracted_fst_files =
                                FStar_All.pipe_right fst_files1
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____7221 =
                                           lowercase_module_name df  in
                                         let uu____7223 =
                                           lowercase_module_name f  in
                                         uu____7221 <> uu____7223) &&
                                          (let uu____7227 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____7227)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____7238 =
                               let uu____7240 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____7240  in
                             if uu____7238
                             then
                               let uu____7243 = output_cmx_file f  in
                               let uu____7245 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____7243 uu____7245
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____7251 = output_krml_file f  in
                             let uu____7253 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____7251
                               uu____7253)))
                        else
                          (let uu____7258 =
                             (let uu____7262 =
                                let uu____7264 = lowercase_module_name f  in
                                has_implementation file_system_map uu____7264
                                 in
                              Prims.op_Negation uu____7262) &&
                               (is_interface f)
                              in
                           if uu____7258
                           then
                             let uu____7267 = output_krml_file f  in
                             let uu____7269 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____7267
                               uu____7269
                           else ()))))));
         (let all_fst_files =
            let uu____7278 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____7278
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____7319 = FStar_Options.should_extract mname  in
                    if uu____7319
                    then
                      let uu____7322 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____7322
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____7349 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____7349));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____7368 =
              let uu____7380 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____7380  in
            match uu____7368 with
            | (exe,deps2,seen) ->
                if seen
                then (exe, deps2)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                   (let deps3 =
                      let uu____7474 =
                        let uu____7478 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____7494 = make_transitive dep1  in
                               match uu____7494 with
                               | (uu____7506,deps3) -> dep1 :: deps3) deps2
                           in
                        FStar_List.flatten uu____7478  in
                      FStar_List.unique uu____7474  in
                    FStar_Util.smap_add transitive_krml f (exe, deps3, true);
                    (exe, deps3)))
             in
          (let uu____7542 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____7567 = make_transitive f  in
                match uu____7567 with
                | (exe,deps2) ->
                    let deps3 =
                      let uu____7588 = FStar_List.unique (f :: deps2)  in
                      FStar_String.concat " " uu____7588  in
                    let wasm =
                      let uu____7597 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____7597 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps3;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps3)) uu____7542);
          (let uu____7606 =
             let uu____7608 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____7608 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____7606);
          (let uu____7627 =
             let uu____7629 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____7629 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____7627);
          (let uu____7647 =
             let uu____7649 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____7649 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____7647)))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____7673 = FStar_Options.dep ()  in
    match uu____7673 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____7683 = deps  in
        (match uu____7683 with
         | Mk (deps1,uu____7685,uu____7686,uu____7687) -> print_graph deps1)
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____7702 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  
let (print_fsmap :
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap -> Prims.string)
  =
  fun fsmap  ->
    FStar_Util.smap_fold fsmap
      (fun k  ->
         fun uu____7757  ->
           fun s  ->
             match uu____7757 with
             | (v0,v1) ->
                 let uu____7786 =
                   let uu____7788 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   Prims.strcat "; " uu____7788  in
                 Prims.strcat s uu____7786) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun uu____7807  ->
    fun module_name  ->
      match uu____7807 with
      | Mk (uu____7810,fsmap,uu____7812,uu____7813) ->
          let uu____7826 =
            let uu____7828 = FStar_Ident.string_of_lid module_name  in
            FStar_String.lowercase uu____7828  in
          has_interface fsmap uu____7826
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun uu____7840  ->
    fun module_name  ->
      match uu____7840 with
      | Mk (uu____7843,uu____7844,uu____7845,all_files) ->
          let m =
            let uu____7861 = FStar_Ident.string_of_lid module_name  in
            FStar_String.lowercase uu____7861  in
          FStar_All.pipe_right all_files
            (FStar_Util.for_some
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____7872 =
                       let uu____7874 = module_name_of_file f  in
                       FStar_String.lowercase uu____7874  in
                     uu____7872 = m)))
  