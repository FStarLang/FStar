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
  fun uu___110_177  ->
    match uu___110_177 with
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
  fun uu___111_336  ->
    match uu___111_336 with
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
  | Mk of (dependence_graph,files_for_module_name,file_name Prims.list)
  FStar_Pervasives_Native.tuple3 
let (uu___is_Mk : deps -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk__item___0 :
  deps ->
    (dependence_graph,files_for_module_name,file_name Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Mk _0 -> _0 
let (deps_try_find :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun uu____451  ->
    fun k  -> match uu____451 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun uu____486  ->
    fun k  ->
      fun v1  -> match uu____486 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____510  -> match uu____510 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____528  ->
    let uu____529 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____529
  
let (empty_deps : deps) =
  let uu____540 =
    let uu____549 = deps_empty ()  in
    let uu____550 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____549, uu____550, [])  in
  Mk uu____540 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___112_565  ->
    match uu___112_565 with
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
      let uu____584 = FStar_Util.smap_try_find file_system_map key  in
      match uu____584 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____606) ->
          let uu____621 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____621
      | FStar_Pervasives_Native.Some
          (uu____622,FStar_Pervasives_Native.Some fn) ->
          let uu____638 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____638
      | uu____639 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____664 = FStar_Util.smap_try_find file_system_map key  in
      match uu____664 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____686) ->
          FStar_Pervasives_Native.Some iface
      | uu____701 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____726 = FStar_Util.smap_try_find file_system_map key  in
      match uu____726 with
      | FStar_Pervasives_Native.Some
          (uu____747,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____763 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____784 = interface_of file_system_map key  in
      FStar_Option.isSome uu____784
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____797 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____797
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____805 =
      let uu____806 = FStar_Options.lax ()  in
      if uu____806
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____805
  
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
                      (let uu____843 = lowercase_module_name fn  in
                       key = uu____843)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____852 = interface_of file_system_map key  in
              (match uu____852 with
               | FStar_Pervasives_Native.None  ->
                   let uu____856 =
                     let uu____861 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____861)  in
                   FStar_Errors.raise_err uu____856
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____864 =
                (cmd_line_has_impl key) &&
                  (let uu____866 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____866)
                 in
              if uu____864
              then
                let uu____869 = FStar_Options.expose_interfaces ()  in
                (if uu____869
                 then
                   let uu____870 =
                     let uu____871 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____871  in
                   maybe_add_suffix uu____870
                 else
                   (let uu____875 =
                      let uu____880 =
                        let uu____881 =
                          let uu____882 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____882  in
                        let uu____885 =
                          let uu____886 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____886  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____881 uu____885
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____880)
                       in
                    FStar_Errors.raise_err uu____875))
              else
                (let uu____890 =
                   let uu____891 = interface_of file_system_map key  in
                   FStar_Option.get uu____891  in
                 maybe_add_suffix uu____890)
          | PreferInterface key ->
              let uu____895 = implementation_of file_system_map key  in
              (match uu____895 with
               | FStar_Pervasives_Native.None  ->
                   let uu____899 =
                     let uu____904 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____904)
                      in
                   FStar_Errors.raise_err uu____899
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____907 = implementation_of file_system_map key  in
              (match uu____907 with
               | FStar_Pervasives_Native.None  ->
                   let uu____911 =
                     let uu____916 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____916)
                      in
                   FStar_Errors.raise_err uu____911
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | FriendImplementation key ->
              let uu____919 = implementation_of file_system_map key  in
              (match uu____919 with
               | FStar_Pervasives_Native.None  ->
                   let uu____923 =
                     let uu____928 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____928)
                      in
                   FStar_Errors.raise_err uu____923
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
          let uu____972 = deps_try_find deps fn  in
          match uu____972 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____986) ->
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
    (let uu____999 =
       let uu____1000 =
         let uu____1001 =
           let uu____1002 =
             let uu____1005 =
               let uu____1008 = deps_keys graph  in
               FStar_List.unique uu____1008  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1017 =
                      let uu____1022 = deps_try_find graph k  in
                      FStar_Util.must uu____1022  in
                    FStar_Pervasives_Native.fst uu____1017  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1005
              in
           FStar_String.concat "\n" uu____1002  in
         Prims.strcat uu____1001 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1000  in
     FStar_Util.write_file "dep.graph" uu____999)
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1057  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1074 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1074  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1100 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1100
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1121 =
              let uu____1126 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1126)  in
            FStar_Errors.raise_err uu____1121)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1172 = FStar_Util.smap_try_find map1 key  in
      match uu____1172 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1209 = is_interface full_path  in
          if uu____1209
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1243 = is_interface full_path  in
          if uu____1243
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1270 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1284  ->
          match uu____1284 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1270);
    FStar_List.iter
      (fun f  ->
         let uu____1295 = lowercase_module_name f  in add_entry uu____1295 f)
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
        (let uu____1316 =
           let uu____1319 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1319  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1345 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1345  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1316);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1483 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1483 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1498 = string_of_lid l last1  in
      FStar_String.lowercase uu____1498
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1504 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1504
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1518 =
        let uu____1519 =
          let uu____1520 =
            let uu____1521 =
              let uu____1524 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1524  in
            FStar_Util.must uu____1521  in
          FStar_String.lowercase uu____1520  in
        uu____1519 <> k'  in
      if uu____1518
      then
        let uu____1525 = FStar_Ident.range_of_lid lid  in
        let uu____1526 =
          let uu____1531 =
            let uu____1532 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1532 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1531)  in
        FStar_Errors.log_issue uu____1525 uu____1526
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1539 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1555 = FStar_Options.prims_basename ()  in
      let uu____1556 =
        let uu____1559 = FStar_Options.pervasives_basename ()  in
        let uu____1560 =
          let uu____1563 = FStar_Options.pervasives_native_basename ()  in
          [uu____1563]  in
        uu____1559 :: uu____1560  in
      uu____1555 :: uu____1556  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1598 =
         let uu____1601 = lowercase_module_name full_filename  in
         namespace_of_module uu____1601  in
       match uu____1598 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____1633 -> d = d'
  
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
        let uu____1836 =
          let uu____1837 =
            let uu____1838 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (dep_subsumed_by d) uu____1838  in
          Prims.op_Negation uu____1837  in
        if uu____1836
        then
          let uu____1906 =
            let uu____1909 = FStar_ST.op_Bang deps1  in d :: uu____1909  in
          FStar_ST.op_Colon_Equals deps1 uu____1906
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2074 = resolve_module_name original_or_working_map key  in
        match uu____2074 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2113 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____2113
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2148 -> false  in
      let record_open_module let_open lid =
        let uu____2162 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2162
        then true
        else
          (if let_open
           then
             (let uu____2165 = FStar_Ident.range_of_lid lid  in
              let uu____2166 =
                let uu____2171 =
                  let uu____2172 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2172  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2171)
                 in
              FStar_Errors.log_issue uu____2165 uu____2166)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2182 = FStar_Ident.range_of_lid lid  in
          let uu____2183 =
            let uu____2188 =
              let uu____2189 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2189
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2188)
             in
          FStar_Errors.log_issue uu____2182 uu____2183
        else ()  in
      let record_open let_open lid =
        let uu____2202 = record_open_module let_open lid  in
        if uu____2202
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2214 =
        match uu____2214 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2221 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2234 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2234  in
        let alias = lowercase_join_longident lid true  in
        let uu____2236 = FStar_Util.smap_try_find original_map alias  in
        match uu____2236 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2290 = FStar_Ident.range_of_lid lid  in
              let uu____2291 =
                let uu____2296 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2296)
                 in
              FStar_Errors.log_issue uu____2290 uu____2291);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2303 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2307 = add_dependence_edge working_map module_name  in
            if uu____2307
            then ()
            else
              (let uu____2309 = FStar_Options.debug_any ()  in
               if uu____2309
               then
                 let uu____2310 = FStar_Ident.range_of_lid lid  in
                 let uu____2311 =
                   let uu____2316 =
                     let uu____2317 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2317
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2316)
                    in
                 FStar_Errors.log_issue uu____2310 uu____2311
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___113_2433 =
         match uu___113_2433 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2442 =
                   let uu____2443 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2443  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2447) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2454 =
                   let uu____2455 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2455  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___114_2464 =
         match uu___114_2464 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.Friend lid ->
             let uu____2468 =
               let uu____2469 = lowercase_join_longident lid true  in
               FriendImplementation uu____2469  in
             add_dep deps uu____2468
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2505 = record_module_alias ident lid  in
             if uu____2505
             then
               let uu____2506 =
                 let uu____2507 = lowercase_join_longident lid true  in
                 PreferInterface uu____2507  in
               add_dep deps uu____2506
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2542,patterms) ->
             FStar_List.iter
               (fun uu____2564  ->
                  match uu____2564 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____2573,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____2579,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2581;
               FStar_Parser_AST.mdest = uu____2582;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2584;
               FStar_Parser_AST.mdest = uu____2585;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2587,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2589;
               FStar_Parser_AST.mdest = uu____2590;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2594,tc,ts) ->
             (if tc then record_lid FStar_Parser_Const.mk_class_lid else ();
              (let ts1 =
                 FStar_List.map
                   (fun uu____2627  ->
                      match uu____2627 with | (x,docnik) -> x) ts
                  in
               FStar_List.iter collect_tycon ts1))
         | FStar_Parser_AST.Exception (uu____2640,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2647 -> ()
         | FStar_Parser_AST.Pragma uu____2648 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2684 =
                 let uu____2685 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2685 > (Prims.parse_int "1")  in
               if uu____2684
               then
                 let uu____2727 =
                   let uu____2732 =
                     let uu____2733 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2733
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2732)  in
                 let uu____2734 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____2727 uu____2734
               else ()))
       
       and collect_tycon uu___115_2736 =
         match uu___115_2736 with
         | FStar_Parser_AST.TyconAbstract (uu____2737,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2749,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2763,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2809  ->
                   match uu____2809 with
                   | (uu____2818,t,uu____2820) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2825,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2884  ->
                   match uu____2884 with
                   | (uu____2897,t,uu____2899,uu____2900) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___116_2909 =
         match uu___116_2909 with
         | FStar_Parser_AST.DefineEffect (uu____2910,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2924,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___117_2935 =
         match uu___117_2935 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2936,t);
             FStar_Parser_AST.brange = uu____2938;
             FStar_Parser_AST.blevel = uu____2939;
             FStar_Parser_AST.aqual = uu____2940;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2943,t);
             FStar_Parser_AST.brange = uu____2945;
             FStar_Parser_AST.blevel = uu____2946;
             FStar_Parser_AST.aqual = uu____2947;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2951;
             FStar_Parser_AST.blevel = uu____2952;
             FStar_Parser_AST.aqual = uu____2953;_} -> collect_term t
         | uu____2956 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___118_2958 =
         match uu___118_2958 with
         | FStar_Const.Const_int
             (uu____2959,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____2974 =
               let uu____2975 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____2975  in
             add_dep deps uu____2974
         | FStar_Const.Const_char uu____3009 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3044 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3078 -> ()
       
       and collect_term' uu___119_3079 =
         match uu___119_3079 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____3088 =
                 let uu____3089 = FStar_Ident.text_of_id s  in
                 uu____3089 = "@"  in
               if uu____3088
               then
                 let uu____3090 =
                   let uu____3091 =
                     let uu____3092 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____3092
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3091  in
                 collect_term' uu____3090
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3094 -> ()
         | FStar_Parser_AST.Uvar uu____3095 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3098) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3128  ->
                   match uu____3128 with | (t,uu____3134) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3144) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3146,patterms,t) ->
             (FStar_List.iter
                (fun uu____3196  ->
                   match uu____3196 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3225 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3234,t1,t2) ->
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
                (fun uu____3330  ->
                   match uu____3330 with | (uu____3335,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3338) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3394,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3398) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3404) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3410,uu____3411) ->
             collect_term t
         | FStar_Parser_AST.Quote (t,uu____3413) -> collect_term t
         | FStar_Parser_AST.Antiquote t -> collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___120_3423 =
         match uu___120_3423 with
         | FStar_Parser_AST.PatWild uu____3424 -> ()
         | FStar_Parser_AST.PatOp uu____3427 -> ()
         | FStar_Parser_AST.PatConst uu____3428 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3436 -> ()
         | FStar_Parser_AST.PatName uu____3443 -> ()
         | FStar_Parser_AST.PatTvar uu____3444 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3458) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3477  ->
                  match uu____3477 with | (uu____3482,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3527 =
         match uu____3527 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3545 = FStar_Parser_Driver.parse_file filename  in
       match uu____3545 with
       | (ast,uu____3565) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3580 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____3580
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3616 = FStar_ST.op_Bang deps  in
             let uu____3664 = FStar_ST.op_Bang mo_roots  in
             (uu____3616, uu____3664))))
  
let (collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap FStar_ST.ref)
  =
  let uu____3739 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____3739 
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
              let uu____3864 = FStar_Options.find_file fn  in
              match uu____3864 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3867 =
                    let uu____3872 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3872)  in
                  FStar_Errors.raise_err uu____3867
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3882 =
        let uu____3883 = deps_try_find dep_graph file_name  in
        uu____3883 = FStar_Pervasives_Native.None  in
      if uu____3882
      then
        let uu____3900 =
          let uu____3909 =
            let uu____3920 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____3920 file_name  in
          match uu____3909 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____3900 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____4025 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____4025
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____4030 =
                let uu____4035 = FStar_List.unique deps1  in
                (uu____4035, White)  in
              deps_add_dep dep_graph file_name uu____4030);
             (let uu____4036 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____4036))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let dep_graph_copy dep_graph1 =
       let uu____4047 = dep_graph1  in
       match uu____4047 with
       | Deps g ->
           let uu____4055 = FStar_Util.smap_copy g  in Deps uu____4055
        in
     let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____4089 =
          let uu____4094 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____4094)  in
        FStar_Errors.raise_err uu____4089)
        in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy dep_graph  in
       let rec aux cycle filename =
         let uu____4121 =
           let uu____4128 = deps_try_find dep_graph1 filename  in
           match uu____4128 with
           | FStar_Pervasives_Native.Some (d,c) -> (d, c)
           | FStar_Pervasives_Native.None  ->
               let uu____4153 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____4153
            in
         match uu____4121 with
         | (direct_deps,color) ->
             let direct_deps1 =
               FStar_All.pipe_right direct_deps
                 (FStar_List.collect
                    (fun x  ->
                       match x with
                       | UseInterface f ->
                           let uu____4176 =
                             implementation_of file_system_map f  in
                           (match uu____4176 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4182 -> [x; UseImplementation f])
                       | PreferInterface f ->
                           let uu____4186 =
                             implementation_of file_system_map f  in
                           (match uu____4186 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4192 -> [x; UseImplementation f])
                       | uu____4195 -> [x]))
                in
             (match color with
              | Gray  -> cycle_detected dep_graph1 cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph1 filename (direct_deps1, Gray);
                   (let uu____4198 =
                      dependences_of file_system_map dep_graph1
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4198);
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
        let rec all_friend_deps_1 dep_graph1 cycle uu____4297 filename =
          match uu____4297 with
          | (all_friends,all_files) ->
              let uu____4327 =
                let uu____4332 = deps_try_find dep_graph1 filename  in
                FStar_Util.must uu____4332  in
              (match uu____4327 with
               | (direct_deps,color) ->
                   (match color with
                    | Gray  ->
                        (cycle_detected dep_graph1 cycle filename;
                         (all_friends, all_files))
                    | Black  -> (all_friends, all_files)
                    | White  ->
                        (deps_add_dep dep_graph1 filename (direct_deps, Gray);
                         (let uu____4371 =
                            let uu____4380 =
                              dependences_of file_system_map dep_graph1
                                all_command_line_files filename
                               in
                            all_friend_deps dep_graph1 cycle
                              (all_friends, all_files) uu____4380
                             in
                          match uu____4371 with
                          | (all_friends1,all_files1) ->
                              (deps_add_dep dep_graph1 filename
                                 (direct_deps, Black);
                               (let uu____4406 =
                                  let uu____4409 =
                                    FStar_List.filter
                                      (fun uu___121_4414  ->
                                         match uu___121_4414 with
                                         | FriendImplementation uu____4415 ->
                                             true
                                         | uu____4416 -> false) direct_deps
                                     in
                                  FStar_List.append uu____4409 all_friends1
                                   in
                                (uu____4406, (filename :: all_files1))))))))
        
        and all_friend_deps dep_graph1 cycle all_friends filenames =
          FStar_List.fold_left
            (fun all_friends1  ->
               fun k  ->
                 all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
            all_friends filenames
         in
        let uu____4457 =
          let uu____4466 = dep_graph_copy dep_graph  in
          all_friend_deps uu____4466 [] ([], []) all_command_line_files  in
        match uu____4457 with
        | (friends,uu____4474) ->
            let widen_deps friends1 deps =
              FStar_All.pipe_right deps
                (FStar_List.map
                   (fun d  ->
                      match d with
                      | PreferInterface f when
                          FStar_List.contains (FriendImplementation f)
                            friends1
                          -> FriendImplementation f
                      | uu____4512 -> d))
               in
            let uu____4513 =
              let uu____4522 = dep_graph  in
              match uu____4522 with
              | Deps dg ->
                  let uu____4538 = deps_empty ()  in
                  (match uu____4538 with
                   | Deps dg' ->
                       (FStar_Util.smap_fold dg
                          (fun filename  ->
                             fun uu____4566  ->
                               fun uu____4567  ->
                                 match uu____4566 with
                                 | (dependences,color) ->
                                     let uu____4574 =
                                       let uu____4579 =
                                         widen_deps friends dependences  in
                                       (uu____4579, color)  in
                                     FStar_Util.smap_add dg' filename
                                       uu____4574) ();
                        all_friend_deps (Deps dg') [] ([], [])
                          all_command_line_files))
               in
            (match uu____4513 with | (uu____4590,all_files) -> all_files)
         in
      let uu____4600 = topological_dependences_of all_cmd_line_files1  in
      (uu____4600, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____4617  ->
    fun f  ->
      match uu____4617 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____4646  ->
    fun fn  ->
      match uu____4646 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____4664 = FStar_Options.find_file fn  in
            match uu____4664 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____4668 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____4679 = FStar_Options.debug_any ()  in
             if uu____4679
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____4690 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____4690
            then
              let uu____4697 =
                let uu____4702 =
                  let uu____4703 =
                    let uu____4704 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____4704  in
                  digest_of_file1 uu____4703  in
                ("interface", uu____4702)  in
              [uu____4697]
            else []  in
          let binary_deps =
            let uu____4723 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____4723
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____4733 =
                      (is_interface fn2) &&
                        (let uu____4735 = lowercase_module_name fn2  in
                         uu____4735 = module_name)
                       in
                    Prims.op_Negation uu____4733))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____4745 = lowercase_module_name fn11  in
                   let uu____4746 = lowercase_module_name fn2  in
                   FStar_String.compare uu____4745 uu____4746) binary_deps
             in
          let rec hash_deps out uu___122_4773 =
            match uu___122_4773 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let digest =
                  let fn3 = cache_file_name fn2  in
                  if FStar_Util.file_exists fn3
                  then
                    let uu____4814 = digest_of_file1 fn3  in
                    FStar_Pervasives_Native.Some uu____4814
                  else
                    (let uu____4816 =
                       let uu____4819 = FStar_Util.basename fn3  in
                       FStar_Options.find_file uu____4819  in
                     match uu____4816 with
                     | FStar_Pervasives_Native.None  ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some fn4 ->
                         let uu____4823 = digest_of_file1 fn4  in
                         FStar_Pervasives_Native.Some uu____4823)
                   in
                (match digest with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____4833 = FStar_Options.debug_any ()  in
                       if uu____4833
                       then
                         let uu____4834 = cache_file_name fn2  in
                         FStar_Util.print2 "%s: missed digest of file %s\n"
                           cache_file uu____4834
                       else ());
                      FStar_Pervasives_Native.None)
                 | FStar_Pervasives_Native.Some dig ->
                     let uu____4843 =
                       let uu____4850 =
                         let uu____4855 = lowercase_module_name fn2  in
                         (uu____4855, dig)  in
                       uu____4850 :: out  in
                     hash_deps uu____4843 deps1)
             in
          hash_deps [] binary_deps1
  
let (print_digest :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string)
  =
  fun dig  ->
    let uu____4881 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4900  ->
              match uu____4900 with
              | (m,d) ->
                  let uu____4907 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4907))
       in
    FStar_All.pipe_right uu____4881 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____4914  ->
    match uu____4914 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4934 =
                  let uu____4939 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4939 FStar_Option.get  in
                match uu____4934 with
                | (f_deps,uu____4961) ->
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
    let uu____4976 = deps  in
    match uu____4976 with
    | Mk (Deps deps1,uu____4978,uu____4979) ->
        let uu____4990 =
          let uu____4991 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun uu____5007  ->
                   fun out  ->
                     match uu____5007 with
                     | (dep1,uu____5018) ->
                         let uu____5019 =
                           let uu____5020 =
                             let uu____5021 =
                               FStar_List.map dep_to_string dep1  in
                             FStar_All.pipe_right uu____5021
                               (FStar_String.concat ";\n\t")
                              in
                           FStar_Util.format2 "%s -> [\n\t%s\n] " k
                             uu____5020
                            in
                         uu____5019 :: out) []
             in
          FStar_All.pipe_right uu____4991 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____4990 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let uu____5033 = deps  in
    match uu____5033 with
    | Mk (deps1,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____5074 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____5074) ||
              (let uu____5078 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____5078)
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
                let uu____5105 =
                  let uu____5108 = FStar_ST.op_Bang order  in ml_file ::
                    uu____5108
                   in
                FStar_ST.op_Colon_Equals order uu____5105
             in
          let rec aux uu___123_5208 =
            match uu___123_5208 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____5226 = deps_try_find deps1 file_name  in
                      (match uu____5226 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____5237 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____5237
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____5239) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____5250 = should_visit lc_module_name  in
                  if uu____5250
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____5255 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____5255);
                     (let uu____5259 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____5259);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____5267 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____5267)
           in
        let keys = deps_keys deps1  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____5330 =
              let uu____5331 =
                let uu____5334 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____5334  in
              FStar_Option.get uu____5331  in
            FStar_Util.replace_chars uu____5330 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____5349 = output_file ".ml" f  in norm_path uu____5349  in
        let output_krml_file f =
          let uu____5356 = output_file ".krml" f  in norm_path uu____5356  in
        let output_cmx_file f =
          let uu____5363 = output_file ".cmx" f  in norm_path uu____5363  in
        let cache_file f =
          let uu____5370 = cache_file_name f  in norm_path uu____5370  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____5415 =
                   let uu____5422 = deps_try_find deps1 f  in
                   FStar_All.pipe_right uu____5422 FStar_Option.get  in
                 match uu____5415 with
                 | (f_deps,uu____5446) ->
                     let iface_deps =
                       let uu____5456 = is_interface f  in
                       if uu____5456
                       then FStar_Pervasives_Native.None
                       else
                         (let uu____5464 =
                            let uu____5467 = lowercase_module_name f  in
                            interface_of file_system_map uu____5467  in
                          match uu____5464 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some iface ->
                              let uu____5475 =
                                let uu____5478 =
                                  let uu____5483 = deps_try_find deps1 iface
                                     in
                                  FStar_Option.get uu____5483  in
                                FStar_Pervasives_Native.fst uu____5478  in
                              FStar_Pervasives_Native.Some uu____5475)
                        in
                     let iface_deps1 =
                       FStar_Util.map_opt iface_deps
                         (FStar_List.filter
                            (fun iface_dep  ->
                               let uu____5508 =
                                 FStar_Util.for_some
                                   (dep_subsumed_by iface_dep) f_deps
                                  in
                               Prims.op_Negation uu____5508))
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
                     ((let uu____5543 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5543
                         norm_f files4);
                      (let already_there =
                         let uu____5547 =
                           let uu____5558 =
                             let uu____5559 = output_file ".krml" f  in
                             norm_path uu____5559  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____5558
                            in
                         match uu____5547 with
                         | FStar_Pervasives_Native.Some
                             (uu____5570,already_there,uu____5572) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____5594 =
                          let uu____5595 = output_file ".krml" f  in
                          norm_path uu____5595  in
                        let uu____5596 =
                          let uu____5605 =
                            let uu____5606 = output_file ".exe" f  in
                            norm_path uu____5606  in
                          let uu____5607 =
                            let uu____5610 =
                              let uu____5613 =
                                let uu____5616 =
                                  deps_of
                                    (Mk
                                       (deps1, file_system_map,
                                         all_cmd_line_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____5624 = output_file ".krml" x
                                        in
                                     norm_path uu____5624) uu____5616
                                 in
                              FStar_List.append already_there uu____5613  in
                            FStar_List.unique uu____5610  in
                          (uu____5605, uu____5607, false)  in
                        FStar_Util.smap_add transitive_krml uu____5594
                          uu____5596);
                       (let uu____5635 = is_implementation f  in
                        if uu____5635
                        then
                          ((let uu____5637 = output_ml_file f  in
                            let uu____5638 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5637
                              uu____5638);
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
                                        (let uu____5688 =
                                           lowercase_module_name df  in
                                         let uu____5689 =
                                           lowercase_module_name f  in
                                         uu____5688 <> uu____5689) &&
                                          (let uu____5691 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____5691)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____5697 =
                               let uu____5698 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____5698  in
                             if uu____5697
                             then
                               let uu____5699 = output_cmx_file f  in
                               let uu____5700 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____5699 uu____5700
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____5702 = output_krml_file f  in
                             let uu____5703 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5702
                               uu____5703)))
                        else
                          (let uu____5705 =
                             (let uu____5708 =
                                let uu____5709 = lowercase_module_name f  in
                                has_implementation file_system_map uu____5709
                                 in
                              Prims.op_Negation uu____5708) &&
                               (is_interface f)
                              in
                           if uu____5705
                           then
                             let uu____5710 = output_krml_file f  in
                             let uu____5711 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5710
                               uu____5711
                           else ()))))));
         (let all_fst_files =
            let uu____5716 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____5716
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5742 = FStar_Options.should_extract mname  in
                    if uu____5742
                    then
                      let uu____5743 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____5743
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5759 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____5759));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____5772 =
              let uu____5781 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____5781  in
            match uu____5772 with
            | (exe,deps2,seen) ->
                if seen
                then (exe, deps2)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                   (let deps3 =
                      let uu____5844 =
                        let uu____5847 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____5859 = make_transitive dep1  in
                               match uu____5859 with
                               | (uu____5868,deps3) -> dep1 :: deps3) deps2
                           in
                        FStar_List.flatten uu____5847  in
                      FStar_List.unique uu____5844  in
                    FStar_Util.smap_add transitive_krml f (exe, deps3, true);
                    (exe, deps3)))
             in
          (let uu____5888 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____5907 = make_transitive f  in
                match uu____5907 with
                | (exe,deps2) ->
                    let deps3 =
                      let uu____5921 = FStar_List.unique (f :: deps2)  in
                      FStar_String.concat " " uu____5921  in
                    let wasm =
                      let uu____5925 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____5925 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps3;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps3)) uu____5888);
          (let uu____5928 =
             let uu____5929 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5929 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5928);
          (let uu____5939 =
             let uu____5940 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5940 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5939);
          (let uu____5949 =
             let uu____5950 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5950 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5949)))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____5964 = FStar_Options.dep ()  in
    match uu____5964 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____5967 = deps  in
        (match uu____5967 with
         | Mk (deps1,uu____5969,uu____5970) -> print_graph deps1)
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____5975 ->
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
         fun uu____6016  ->
           fun s  ->
             match uu____6016 with
             | (v0,v1) ->
                 let uu____6036 =
                   let uu____6037 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   Prims.strcat "; " uu____6037  in
                 Prims.strcat s uu____6036) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun uu____6046  ->
    fun module_name  ->
      match uu____6046 with
      | Mk (uu____6048,fsmap,uu____6050) ->
          let uu____6055 =
            let uu____6056 = FStar_Ident.string_of_lid module_name  in
            FStar_String.lowercase uu____6056  in
          has_interface fsmap uu____6055
  