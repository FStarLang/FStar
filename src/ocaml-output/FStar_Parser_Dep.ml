open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____6 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____12 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____18 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____34 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____40 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____46 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____52 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____58 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____86 =
             (l > lext) &&
               (let uu____98 = FStar_String.substring f (l - lext) lext  in
                uu____98 = ext)
              in
           if uu____86
           then
             let uu____115 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____115
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____127 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____127 with
    | (FStar_Pervasives_Native.Some m)::uu____137 ->
        FStar_Pervasives_Native.Some m
    | uu____144 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____154 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____154 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____163 = is_interface f  in Prims.op_Negation uu____163 
let list_of_option :
  'Auu____168 .
    'Auu____168 FStar_Pervasives_Native.option -> 'Auu____168 Prims.list
  =
  fun uu___111_177  ->
    match uu___111_177 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____185 .
    ('Auu____185 FStar_Pervasives_Native.option,'Auu____185
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____185 Prims.list
  =
  fun uu____200  ->
    match uu____200 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____224 =
      let uu____227 = FStar_Util.basename f  in
      check_and_strip_suffix uu____227  in
    match uu____224 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____229 =
          let uu____234 = FStar_Util.format1 "not a valid FStar file: %s\n" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____234)  in
        FStar_Errors.raise_err uu____229
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____240 = module_name_of_file f  in
    FStar_String.lowercase uu____240
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____249 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____249 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____252 ->
        let uu____255 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____255
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____282 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____296 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____310 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____324 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___112_336  ->
    match uu___112_336 with
    | UseInterface f -> Prims.strcat "UseInterface " f
    | PreferInterface f -> Prims.strcat "PreferInterface " f
    | UseImplementation f -> Prims.strcat "UseImplementation " f
    | FriendImplementation f -> Prims.strcat "UseImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____345 . unit -> 'Auu____345 Prims.list =
  fun uu____348  -> [] 
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
  fun uu____467  ->
    fun k  -> match uu____467 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun uu____502  ->
    fun k  ->
      fun v1  -> match uu____502 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____526  -> match uu____526 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____544  ->
    let uu____545 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____545
  
let (empty_deps : deps) =
  let uu____556 =
    let uu____569 = deps_empty ()  in
    let uu____570 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____569, uu____570, [], [])  in
  Mk uu____556 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___113_587  ->
    match uu___113_587 with
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
      let uu____606 = FStar_Util.smap_try_find file_system_map key  in
      match uu____606 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____628) ->
          let uu____643 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____643
      | FStar_Pervasives_Native.Some
          (uu____644,FStar_Pervasives_Native.Some fn) ->
          let uu____660 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____660
      | uu____661 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____686 = FStar_Util.smap_try_find file_system_map key  in
      match uu____686 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____708) ->
          FStar_Pervasives_Native.Some iface
      | uu____723 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____748 = FStar_Util.smap_try_find file_system_map key  in
      match uu____748 with
      | FStar_Pervasives_Native.Some
          (uu____769,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____785 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____806 = interface_of file_system_map key  in
      FStar_Option.isSome uu____806
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____819 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____819
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____827 =
      let uu____828 = FStar_Options.lax ()  in
      if uu____828
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____827
  
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
                      (let uu____865 = lowercase_module_name fn  in
                       key = uu____865)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____874 = interface_of file_system_map key  in
              (match uu____874 with
               | FStar_Pervasives_Native.None  ->
                   let uu____878 =
                     let uu____883 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____883)  in
                   FStar_Errors.raise_err uu____878
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____886 =
                (cmd_line_has_impl key) &&
                  (let uu____888 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____888)
                 in
              if uu____886
              then
                let uu____891 = FStar_Options.expose_interfaces ()  in
                (if uu____891
                 then
                   let uu____892 =
                     let uu____893 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____893  in
                   maybe_add_suffix uu____892
                 else
                   (let uu____897 =
                      let uu____902 =
                        let uu____903 =
                          let uu____904 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____904  in
                        let uu____907 =
                          let uu____908 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____908  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____903 uu____907
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____902)
                       in
                    FStar_Errors.raise_err uu____897))
              else
                (let uu____912 =
                   let uu____913 = interface_of file_system_map key  in
                   FStar_Option.get uu____913  in
                 maybe_add_suffix uu____912)
          | PreferInterface key ->
              let uu____917 = implementation_of file_system_map key  in
              (match uu____917 with
               | FStar_Pervasives_Native.None  ->
                   let uu____921 =
                     let uu____926 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____926)
                      in
                   FStar_Errors.raise_err uu____921
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____929 = implementation_of file_system_map key  in
              (match uu____929 with
               | FStar_Pervasives_Native.None  ->
                   let uu____933 =
                     let uu____938 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____938)
                      in
                   FStar_Errors.raise_err uu____933
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | FriendImplementation key ->
              let uu____941 = implementation_of file_system_map key  in
              (match uu____941 with
               | FStar_Pervasives_Native.None  ->
                   let uu____945 =
                     let uu____950 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____950)
                      in
                   FStar_Errors.raise_err uu____945
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
          let uu____994 = deps_try_find deps fn  in
          match uu____994 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____1008) ->
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
    (let uu____1021 =
       let uu____1022 =
         let uu____1023 =
           let uu____1024 =
             let uu____1027 =
               let uu____1030 = deps_keys graph  in
               FStar_List.unique uu____1030  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1039 =
                      let uu____1044 = deps_try_find graph k  in
                      FStar_Util.must uu____1044  in
                    FStar_Pervasives_Native.fst uu____1039  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1027
              in
           FStar_String.concat "\n" uu____1024  in
         Prims.strcat uu____1023 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1022  in
     FStar_Util.write_file "dep.graph" uu____1021)
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1079  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1096 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1096  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1122 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1122
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1143 =
              let uu____1148 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1148)  in
            FStar_Errors.raise_err uu____1143)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1194 = FStar_Util.smap_try_find map1 key  in
      match uu____1194 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1231 = is_interface full_path  in
          if uu____1231
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1265 = is_interface full_path  in
          if uu____1265
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1292 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1306  ->
          match uu____1306 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1292);
    FStar_List.iter
      (fun f  ->
         let uu____1317 = lowercase_module_name f  in add_entry uu____1317 f)
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
        (let uu____1338 =
           let uu____1341 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1341  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1367 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1367  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1338);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1505 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1505 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1520 = string_of_lid l last1  in
      FStar_String.lowercase uu____1520
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1526 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1526
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1540 =
        let uu____1541 =
          let uu____1542 =
            let uu____1543 =
              let uu____1546 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1546  in
            FStar_Util.must uu____1543  in
          FStar_String.lowercase uu____1542  in
        uu____1541 <> k'  in
      if uu____1540
      then
        let uu____1547 = FStar_Ident.range_of_lid lid  in
        let uu____1548 =
          let uu____1553 =
            let uu____1554 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1554 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1553)  in
        FStar_Errors.log_issue uu____1547 uu____1548
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1561 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1577 = FStar_Options.prims_basename ()  in
      let uu____1578 =
        let uu____1581 = FStar_Options.pervasives_basename ()  in
        let uu____1582 =
          let uu____1585 = FStar_Options.pervasives_native_basename ()  in
          [uu____1585]  in
        uu____1581 :: uu____1582  in
      uu____1577 :: uu____1578  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1620 =
         let uu____1623 = lowercase_module_name full_filename  in
         namespace_of_module uu____1623  in
       match uu____1620 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____1655 -> d = d'
  
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
        let uu____1858 =
          let uu____1859 =
            let uu____1860 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (dep_subsumed_by d) uu____1860  in
          Prims.op_Negation uu____1859  in
        if uu____1858
        then
          let uu____1928 =
            let uu____1931 = FStar_ST.op_Bang deps1  in d :: uu____1931  in
          FStar_ST.op_Colon_Equals deps1 uu____1928
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2096 = resolve_module_name original_or_working_map key  in
        match uu____2096 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2135 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____2135
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2170 -> false  in
      let record_open_module let_open lid =
        let uu____2184 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2184
        then true
        else
          (if let_open
           then
             (let uu____2187 = FStar_Ident.range_of_lid lid  in
              let uu____2188 =
                let uu____2193 =
                  let uu____2194 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2194  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2193)
                 in
              FStar_Errors.log_issue uu____2187 uu____2188)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2204 = FStar_Ident.range_of_lid lid  in
          let uu____2205 =
            let uu____2210 =
              let uu____2211 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2211
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2210)
             in
          FStar_Errors.log_issue uu____2204 uu____2205
        else ()  in
      let record_open let_open lid =
        let uu____2224 = record_open_module let_open lid  in
        if uu____2224
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2236 =
        match uu____2236 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2243 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2256 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2256  in
        let alias = lowercase_join_longident lid true  in
        let uu____2258 = FStar_Util.smap_try_find original_map alias  in
        match uu____2258 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2312 = FStar_Ident.range_of_lid lid  in
              let uu____2313 =
                let uu____2318 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2318)
                 in
              FStar_Errors.log_issue uu____2312 uu____2313);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2325 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2329 = add_dependence_edge working_map module_name  in
            if uu____2329
            then ()
            else
              (let uu____2331 = FStar_Options.debug_any ()  in
               if uu____2331
               then
                 let uu____2332 = FStar_Ident.range_of_lid lid  in
                 let uu____2333 =
                   let uu____2338 =
                     let uu____2339 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2339
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2338)
                    in
                 FStar_Errors.log_issue uu____2332 uu____2333
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___114_2455 =
         match uu___114_2455 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2464 =
                   let uu____2465 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2465  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2469) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2476 =
                   let uu____2477 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2477  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___115_2486 =
         match uu___115_2486 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.Friend lid ->
             let uu____2490 =
               let uu____2491 = lowercase_join_longident lid true  in
               FriendImplementation uu____2491  in
             add_dep deps uu____2490
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2527 = record_module_alias ident lid  in
             if uu____2527
             then
               let uu____2528 =
                 let uu____2529 = lowercase_join_longident lid true  in
                 PreferInterface uu____2529  in
               add_dep deps uu____2528
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2564,patterms) ->
             FStar_List.iter
               (fun uu____2586  ->
                  match uu____2586 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____2595,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____2601,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2603;
               FStar_Parser_AST.mdest = uu____2604;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2606;
               FStar_Parser_AST.mdest = uu____2607;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2609,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2611;
               FStar_Parser_AST.mdest = uu____2612;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2616,tc,ts) ->
             (if tc then record_lid FStar_Parser_Const.mk_class_lid else ();
              (let ts1 =
                 FStar_List.map
                   (fun uu____2649  ->
                      match uu____2649 with | (x,docnik) -> x) ts
                  in
               FStar_List.iter collect_tycon ts1))
         | FStar_Parser_AST.Exception (uu____2662,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2669 -> ()
         | FStar_Parser_AST.Pragma uu____2670 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2706 =
                 let uu____2707 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2707 > (Prims.parse_int "1")  in
               if uu____2706
               then
                 let uu____2749 =
                   let uu____2754 =
                     let uu____2755 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2755
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2754)  in
                 let uu____2756 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____2749 uu____2756
               else ()))
       
       and collect_tycon uu___116_2758 =
         match uu___116_2758 with
         | FStar_Parser_AST.TyconAbstract (uu____2759,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2771,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2785,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2831  ->
                   match uu____2831 with
                   | (uu____2840,t,uu____2842) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2847,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2906  ->
                   match uu____2906 with
                   | (uu____2919,t,uu____2921,uu____2922) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___117_2931 =
         match uu___117_2931 with
         | FStar_Parser_AST.DefineEffect (uu____2932,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2946,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___118_2957 =
         match uu___118_2957 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2958,t);
             FStar_Parser_AST.brange = uu____2960;
             FStar_Parser_AST.blevel = uu____2961;
             FStar_Parser_AST.aqual = uu____2962;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2965,t);
             FStar_Parser_AST.brange = uu____2967;
             FStar_Parser_AST.blevel = uu____2968;
             FStar_Parser_AST.aqual = uu____2969;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2973;
             FStar_Parser_AST.blevel = uu____2974;
             FStar_Parser_AST.aqual = uu____2975;_} -> collect_term t
         | uu____2978 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___119_2980 =
         match uu___119_2980 with
         | FStar_Const.Const_int
             (uu____2981,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____2996 =
               let uu____2997 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____2997  in
             add_dep deps uu____2996
         | FStar_Const.Const_char uu____3031 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3066 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3100 -> ()
       
       and collect_term' uu___120_3101 =
         match uu___120_3101 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____3110 =
                 let uu____3111 = FStar_Ident.text_of_id s  in
                 uu____3111 = "@"  in
               if uu____3110
               then
                 let uu____3112 =
                   let uu____3113 =
                     let uu____3114 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____3114
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3113  in
                 collect_term' uu____3112
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3116 -> ()
         | FStar_Parser_AST.Uvar uu____3117 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3120) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3150  ->
                   match uu____3150 with | (t,uu____3156) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3166) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3168,patterms,t) ->
             (FStar_List.iter
                (fun uu____3218  ->
                   match uu____3218 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3247 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3256,t1,t2) ->
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
                (fun uu____3352  ->
                   match uu____3352 with | (uu____3357,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3360) -> collect_term t
         | FStar_Parser_AST.Product (binders,t) ->
             (collect_binders binders; collect_term t)
         | FStar_Parser_AST.Sum (binders,t) ->
             (collect_binders binders; collect_term t)
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
         | FStar_Parser_AST.NamedTyp (uu____3416,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3420) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3426) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3432,uu____3433) ->
             collect_term t
         | FStar_Parser_AST.Quote (t,uu____3435) -> collect_term t
         | FStar_Parser_AST.Antiquote t -> collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___121_3445 =
         match uu___121_3445 with
         | FStar_Parser_AST.PatWild uu____3446 -> ()
         | FStar_Parser_AST.PatOp uu____3449 -> ()
         | FStar_Parser_AST.PatConst uu____3450 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3458 -> ()
         | FStar_Parser_AST.PatName uu____3465 -> ()
         | FStar_Parser_AST.PatTvar uu____3466 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3480) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3499  ->
                  match uu____3499 with | (uu____3504,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3549 =
         match uu____3549 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3567 = FStar_Parser_Driver.parse_file filename  in
       match uu____3567 with
       | (ast,uu____3587) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3602 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____3602
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3638 = FStar_ST.op_Bang deps  in
             let uu____3686 = FStar_ST.op_Bang mo_roots  in
             (uu____3638, uu____3686))))
  
let (collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap FStar_ST.ref)
  =
  let uu____3761 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____3761 
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
              let uu____3886 = FStar_Options.find_file fn  in
              match uu____3886 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3889 =
                    let uu____3894 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3894)  in
                  FStar_Errors.raise_err uu____3889
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3904 =
        let uu____3905 = deps_try_find dep_graph file_name  in
        uu____3905 = FStar_Pervasives_Native.None  in
      if uu____3904
      then
        let uu____3922 =
          let uu____3931 =
            let uu____3942 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____3942 file_name  in
          match uu____3931 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____3922 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____4047 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____4047
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____4052 =
                let uu____4057 = FStar_List.unique deps1  in
                (uu____4057, White)  in
              deps_add_dep dep_graph file_name uu____4052);
             (let uu____4058 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____4058))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let dep_graph_copy dep_graph1 =
       let uu____4069 = dep_graph1  in
       match uu____4069 with
       | Deps g ->
           let uu____4077 = FStar_Util.smap_copy g  in Deps uu____4077
        in
     let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____4111 =
          let uu____4116 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____4116)  in
        FStar_Errors.raise_err uu____4111)
        in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy dep_graph  in
       let rec aux cycle filename =
         let uu____4143 =
           let uu____4150 = deps_try_find dep_graph1 filename  in
           match uu____4150 with
           | FStar_Pervasives_Native.Some (d,c) -> (d, c)
           | FStar_Pervasives_Native.None  ->
               let uu____4175 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____4175
            in
         match uu____4143 with
         | (direct_deps,color) ->
             let direct_deps1 =
               FStar_All.pipe_right direct_deps
                 (FStar_List.collect
                    (fun x  ->
                       match x with
                       | UseInterface f ->
                           let uu____4198 =
                             implementation_of file_system_map f  in
                           (match uu____4198 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4204 -> [x; UseImplementation f])
                       | PreferInterface f ->
                           let uu____4208 =
                             implementation_of file_system_map f  in
                           (match uu____4208 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4214 -> [x; UseImplementation f])
                       | uu____4217 -> [x]))
                in
             (match color with
              | Gray  -> cycle_detected dep_graph1 cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph1 filename (direct_deps1, Gray);
                   (let uu____4220 =
                      dependences_of file_system_map dep_graph1
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4220);
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
        let rec all_friend_deps_1 dep_graph1 cycle uu____4319 filename =
          match uu____4319 with
          | (all_friends,all_files) ->
              let uu____4349 =
                let uu____4354 = deps_try_find dep_graph1 filename  in
                FStar_Util.must uu____4354  in
              (match uu____4349 with
               | (direct_deps,color) ->
                   (match color with
                    | Gray  ->
                        (cycle_detected dep_graph1 cycle filename;
                         (all_friends, all_files))
                    | Black  -> (all_friends, all_files)
                    | White  ->
                        (deps_add_dep dep_graph1 filename (direct_deps, Gray);
                         (let uu____4393 =
                            let uu____4402 =
                              dependences_of file_system_map dep_graph1
                                all_command_line_files filename
                               in
                            all_friend_deps dep_graph1 cycle
                              (all_friends, all_files) uu____4402
                             in
                          match uu____4393 with
                          | (all_friends1,all_files1) ->
                              (deps_add_dep dep_graph1 filename
                                 (direct_deps, Black);
                               (let uu____4428 =
                                  let uu____4431 =
                                    FStar_List.filter
                                      (fun uu___122_4436  ->
                                         match uu___122_4436 with
                                         | FriendImplementation uu____4437 ->
                                             true
                                         | uu____4438 -> false) direct_deps
                                     in
                                  FStar_List.append uu____4431 all_friends1
                                   in
                                (uu____4428, (filename :: all_files1))))))))
        
        and all_friend_deps dep_graph1 cycle all_friends filenames =
          FStar_List.fold_left
            (fun all_friends1  ->
               fun k  ->
                 all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
            all_friends filenames
         in
        let uu____4479 =
          let uu____4488 = dep_graph_copy dep_graph  in
          all_friend_deps uu____4488 [] ([], []) all_command_line_files  in
        match uu____4479 with
        | (friends,uu____4496) ->
            let widen_deps friends1 deps =
              FStar_All.pipe_right deps
                (FStar_List.map
                   (fun d  ->
                      match d with
                      | PreferInterface f when
                          FStar_List.contains (FriendImplementation f)
                            friends1
                          -> FriendImplementation f
                      | uu____4534 -> d))
               in
            let uu____4535 =
              let uu____4544 = dep_graph  in
              match uu____4544 with
              | Deps dg ->
                  let uu____4560 = deps_empty ()  in
                  (match uu____4560 with
                   | Deps dg' ->
                       (FStar_Util.smap_fold dg
                          (fun filename  ->
                             fun uu____4588  ->
                               fun uu____4589  ->
                                 match uu____4588 with
                                 | (dependences,color) ->
                                     let uu____4596 =
                                       let uu____4601 =
                                         widen_deps friends dependences  in
                                       (uu____4601, color)  in
                                     FStar_Util.smap_add dg' filename
                                       uu____4596) ();
                        all_friend_deps (Deps dg') [] ([], [])
                          all_command_line_files))
               in
            (match uu____4535 with | (uu____4612,all_files) -> all_files)
         in
      let all_files = topological_dependences_of all_cmd_line_files1  in
      (all_files,
        (Mk (dep_graph, file_system_map, all_cmd_line_files1, all_files)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____4641  ->
    fun f  ->
      match uu____4641 with
      | Mk (deps,file_system_map,all_cmd_line_files,uu____4648) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____4675  ->
    fun fn  ->
      match uu____4675 with
      | Mk (deps,file_system_map,all_cmd_line_files,uu____4688) ->
          let fn1 =
            let uu____4698 = FStar_Options.find_file fn  in
            match uu____4698 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____4702 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____4713 = FStar_Options.debug_any ()  in
             if uu____4713
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____4724 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____4724
            then
              let uu____4731 =
                let uu____4736 =
                  let uu____4737 =
                    let uu____4738 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____4738  in
                  digest_of_file1 uu____4737  in
                ("interface", uu____4736)  in
              [uu____4731]
            else []  in
          let binary_deps =
            let uu____4757 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____4757
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____4767 =
                      (is_interface fn2) &&
                        (let uu____4769 = lowercase_module_name fn2  in
                         uu____4769 = module_name)
                       in
                    Prims.op_Negation uu____4767))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____4779 = lowercase_module_name fn11  in
                   let uu____4780 = lowercase_module_name fn2  in
                   FStar_String.compare uu____4779 uu____4780) binary_deps
             in
          let rec hash_deps out uu___123_4807 =
            match uu___123_4807 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let digest =
                  let fn3 = cache_file_name fn2  in
                  if FStar_Util.file_exists fn3
                  then
                    let uu____4848 = digest_of_file1 fn3  in
                    FStar_Pervasives_Native.Some uu____4848
                  else
                    (let uu____4850 =
                       let uu____4853 = FStar_Util.basename fn3  in
                       FStar_Options.find_file uu____4853  in
                     match uu____4850 with
                     | FStar_Pervasives_Native.None  ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some fn4 ->
                         let uu____4857 = digest_of_file1 fn4  in
                         FStar_Pervasives_Native.Some uu____4857)
                   in
                (match digest with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____4867 = FStar_Options.debug_any ()  in
                       if uu____4867
                       then
                         let uu____4868 = cache_file_name fn2  in
                         FStar_Util.print2 "%s: missed digest of file %s\n"
                           cache_file uu____4868
                       else ());
                      FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.Some dig ->
                     let uu____4877 =
                       let uu____4884 =
                         let uu____4889 = lowercase_module_name fn2  in
                         (uu____4889, dig)  in
                       uu____4884 :: out  in
                     hash_deps uu____4877 deps1)
             in
          hash_deps [] binary_deps1
  
let (print_digest :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string)
  =
  fun dig  ->
    let uu____4915 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4934  ->
              match uu____4934 with
              | (m,d) ->
                  let uu____4941 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4941))
       in
    FStar_All.pipe_right uu____4915 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____4948  ->
    match uu____4948 with
    | Mk (deps,file_system_map,all_cmd_line_files,uu____4952) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4973 =
                  let uu____4978 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4978 FStar_Option.get  in
                match uu____4973 with
                | (f_deps,uu____5000) ->
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
    let uu____5015 = deps  in
    match uu____5015 with
    | Mk (Deps deps1,uu____5017,uu____5018,uu____5019) ->
        let uu____5034 =
          let uu____5035 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun uu____5051  ->
                   fun out  ->
                     match uu____5051 with
                     | (dep1,uu____5062) ->
                         let uu____5063 =
                           let uu____5064 =
                             let uu____5065 =
                               FStar_List.map dep_to_string dep1  in
                             FStar_All.pipe_right uu____5065
                               (FStar_String.concat ";\n\t")
                              in
                           FStar_Util.format2 "%s -> [\n\t%s\n] " k
                             uu____5064
                            in
                         uu____5063 :: out) []
             in
          FStar_All.pipe_right uu____5035 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____5034 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let uu____5077 = deps  in
    match uu____5077 with
    | Mk (deps1,file_system_map,all_cmd_line_files,all_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____5123 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____5123) ||
              (let uu____5127 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____5127)
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
                let uu____5154 =
                  let uu____5157 = FStar_ST.op_Bang order  in ml_file ::
                    uu____5157
                   in
                FStar_ST.op_Colon_Equals order uu____5154
             in
          let rec aux uu___124_5257 =
            match uu___124_5257 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____5275 = deps_try_find deps1 file_name  in
                      (match uu____5275 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____5286 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____5286
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____5288) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____5299 = should_visit lc_module_name  in
                  if uu____5299
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____5304 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____5304);
                     (let uu____5308 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____5308);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____5316 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____5316)
           in
        let keys = deps_keys deps1  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____5379 =
              let uu____5380 =
                let uu____5383 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____5383  in
              FStar_Option.get uu____5380  in
            FStar_Util.replace_chars uu____5379 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____5398 = output_file ".ml" f  in norm_path uu____5398  in
        let output_krml_file f =
          let uu____5405 = output_file ".krml" f  in norm_path uu____5405  in
        let output_cmx_file f =
          let uu____5412 = output_file ".cmx" f  in norm_path uu____5412  in
        let cache_file f =
          let uu____5419 = cache_file_name f  in norm_path uu____5419  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____5464 =
                   let uu____5471 = deps_try_find deps1 f  in
                   FStar_All.pipe_right uu____5471 FStar_Option.get  in
                 match uu____5464 with
                 | (f_deps,uu____5495) ->
                     let iface_deps =
                       let uu____5505 = is_interface f  in
                       if uu____5505
                       then FStar_Pervasives_Native.None
                       else
                         (let uu____5513 =
                            let uu____5516 = lowercase_module_name f  in
                            interface_of file_system_map uu____5516  in
                          match uu____5513 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some iface ->
                              let uu____5524 =
                                let uu____5527 =
                                  let uu____5532 = deps_try_find deps1 iface
                                     in
                                  FStar_Option.get uu____5532  in
                                FStar_Pervasives_Native.fst uu____5527  in
                              FStar_Pervasives_Native.Some uu____5524)
                        in
                     let iface_deps1 =
                       FStar_Util.map_opt iface_deps
                         (FStar_List.filter
                            (fun iface_dep  ->
                               let uu____5557 =
                                 FStar_Util.for_some
                                   (dep_subsumed_by iface_dep) f_deps
                                  in
                               Prims.op_Negation uu____5557))
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
                     ((let uu____5592 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5592
                         norm_f files4);
                      (let already_there =
                         let uu____5596 =
                           let uu____5607 =
                             let uu____5608 = output_file ".krml" f  in
                             norm_path uu____5608  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____5607
                            in
                         match uu____5596 with
                         | FStar_Pervasives_Native.Some
                             (uu____5619,already_there,uu____5621) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____5643 =
                          let uu____5644 = output_file ".krml" f  in
                          norm_path uu____5644  in
                        let uu____5645 =
                          let uu____5654 =
                            let uu____5655 = output_file ".exe" f  in
                            norm_path uu____5655  in
                          let uu____5656 =
                            let uu____5659 =
                              let uu____5662 =
                                let uu____5665 =
                                  deps_of
                                    (Mk
                                       (deps1, file_system_map,
                                         all_cmd_line_files, all_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____5675 = output_file ".krml" x
                                        in
                                     norm_path uu____5675) uu____5665
                                 in
                              FStar_List.append already_there uu____5662  in
                            FStar_List.unique uu____5659  in
                          (uu____5654, uu____5656, false)  in
                        FStar_Util.smap_add transitive_krml uu____5643
                          uu____5645);
                       (let uu____5686 = is_implementation f  in
                        if uu____5686
                        then
                          ((let uu____5688 = output_ml_file f  in
                            let uu____5689 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5688
                              uu____5689);
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
                                        (let uu____5739 =
                                           lowercase_module_name df  in
                                         let uu____5740 =
                                           lowercase_module_name f  in
                                         uu____5739 <> uu____5740) &&
                                          (let uu____5742 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____5742)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____5748 =
                               let uu____5749 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____5749  in
                             if uu____5748
                             then
                               let uu____5750 = output_cmx_file f  in
                               let uu____5751 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____5750 uu____5751
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____5753 = output_krml_file f  in
                             let uu____5754 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5753
                               uu____5754)))
                        else
                          (let uu____5756 =
                             (let uu____5759 =
                                let uu____5760 = lowercase_module_name f  in
                                has_implementation file_system_map uu____5760
                                 in
                              Prims.op_Negation uu____5759) &&
                               (is_interface f)
                              in
                           if uu____5756
                           then
                             let uu____5761 = output_krml_file f  in
                             let uu____5762 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5761
                               uu____5762
                           else ()))))));
         (let all_fst_files =
            let uu____5767 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____5767
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5793 = FStar_Options.should_extract mname  in
                    if uu____5793
                    then
                      let uu____5794 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____5794
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5810 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____5810));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____5823 =
              let uu____5832 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____5832  in
            match uu____5823 with
            | (exe,deps2,seen) ->
                if seen
                then (exe, deps2)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                   (let deps3 =
                      let uu____5895 =
                        let uu____5898 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____5910 = make_transitive dep1  in
                               match uu____5910 with
                               | (uu____5919,deps3) -> dep1 :: deps3) deps2
                           in
                        FStar_List.flatten uu____5898  in
                      FStar_List.unique uu____5895  in
                    FStar_Util.smap_add transitive_krml f (exe, deps3, true);
                    (exe, deps3)))
             in
          (let uu____5939 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____5958 = make_transitive f  in
                match uu____5958 with
                | (exe,deps2) ->
                    let deps3 =
                      let uu____5972 = FStar_List.unique (f :: deps2)  in
                      FStar_String.concat " " uu____5972  in
                    let wasm =
                      let uu____5976 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____5976 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps3;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps3)) uu____5939);
          (let uu____5979 =
             let uu____5980 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5980 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5979);
          (let uu____5990 =
             let uu____5991 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5991 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5990);
          (let uu____6000 =
             let uu____6001 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____6001 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____6000)))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____6015 = FStar_Options.dep ()  in
    match uu____6015 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____6018 = deps  in
        (match uu____6018 with
         | Mk (deps1,uu____6020,uu____6021,uu____6022) -> print_graph deps1)
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____6031 ->
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
         fun uu____6072  ->
           fun s  ->
             match uu____6072 with
             | (v0,v1) ->
                 let uu____6092 =
                   let uu____6093 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   Prims.strcat "; " uu____6093  in
                 Prims.strcat s uu____6092) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun uu____6102  ->
    fun module_name  ->
      match uu____6102 with
      | Mk (uu____6104,fsmap,uu____6106,uu____6107) ->
          let uu____6116 =
            let uu____6117 = FStar_Ident.string_of_lid module_name  in
            FStar_String.lowercase uu____6117  in
          has_interface fsmap uu____6116
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun uu____6126  ->
    fun module_name  ->
      match uu____6126 with
      | Mk (uu____6128,uu____6129,uu____6130,all_files) ->
          let m =
            let uu____6141 = FStar_Ident.string_of_lid module_name  in
            FStar_String.lowercase uu____6141  in
          FStar_All.pipe_right all_files
            (FStar_Util.for_some
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____6147 =
                       let uu____6148 = module_name_of_file f  in
                       FStar_String.lowercase uu____6148  in
                     uu____6147 = m)))
  