open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut [@@deriving show]
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
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White 
  | Gray 
  | Black [@@deriving show]
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____34 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____40 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____46 -> false 
type open_kind =
  | Open_module 
  | Open_namespace [@@deriving show]
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
  fun uu___55_177  ->
    match uu___55_177 with
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
  
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name [@@deriving show]
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____274 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____288 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____302 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences : 'Auu____314 . unit -> 'Auu____314 Prims.list =
  fun uu____317  -> [] 
type dependence_graph =
  | Deps of (dependences,color) FStar_Pervasives_Native.tuple2
  FStar_Util.smap [@@deriving show]
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee  -> true 
let (__proj__Deps__item___0 :
  dependence_graph ->
    (dependences,color) FStar_Pervasives_Native.tuple2 FStar_Util.smap)
  = fun projectee  -> match projectee with | Deps _0 -> _0 
type deps =
  | Mk of (dependence_graph,files_for_module_name,file_name Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
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
  fun uu____418  ->
    fun k  -> match uu____418 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun uu____453  ->
    fun k  ->
      fun v1  -> match uu____453 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____477  -> match uu____477 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____495  ->
    let uu____496 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____496
  
let (empty_deps : deps) =
  let uu____507 =
    let uu____516 = deps_empty ()  in
    let uu____517 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____516, uu____517, [])  in
  Mk uu____507 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___56_552  ->
    match uu___56_552 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____570 = FStar_Util.smap_try_find file_system_map key  in
      match uu____570 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____592) ->
          let uu____607 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____607
      | FStar_Pervasives_Native.Some
          (uu____608,FStar_Pervasives_Native.Some fn) ->
          let uu____624 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____624
      | uu____625 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____650 = FStar_Util.smap_try_find file_system_map key  in
      match uu____650 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____672) ->
          FStar_Pervasives_Native.Some iface
      | uu____687 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____712 = FStar_Util.smap_try_find file_system_map key  in
      match uu____712 with
      | FStar_Pervasives_Native.Some
          (uu____733,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____749 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____770 = interface_of file_system_map key  in
      FStar_Option.isSome uu____770
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____783 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____783
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____791 =
      let uu____792 = FStar_Options.lax ()  in
      if uu____792
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____791
  
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
                      (let uu____829 = lowercase_module_name fn  in
                       key = uu____829)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____838 = interface_of file_system_map key  in
              (match uu____838 with
               | FStar_Pervasives_Native.None  ->
                   let uu____842 =
                     let uu____847 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____847)  in
                   FStar_Errors.raise_err uu____842
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____851 =
                (cmd_line_has_impl key) &&
                  (let uu____853 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____853)
                 in
              if uu____851
              then
                let uu____856 = FStar_Options.expose_interfaces ()  in
                (if uu____856
                 then
                   let uu____857 =
                     let uu____858 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____858  in
                   maybe_add_suffix uu____857
                 else
                   (let uu____862 =
                      let uu____867 =
                        let uu____868 =
                          let uu____869 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____869  in
                        let uu____872 =
                          let uu____873 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____873  in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____868 uu____872
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____867)
                       in
                    FStar_Errors.raise_err uu____862))
              else
                (let uu____877 =
                   let uu____878 = interface_of file_system_map key  in
                   FStar_Option.get uu____878  in
                 maybe_add_suffix uu____877)
          | PreferInterface key ->
              let uu____882 = implementation_of file_system_map key  in
              (match uu____882 with
               | FStar_Pervasives_Native.None  ->
                   let uu____886 =
                     let uu____891 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____891)
                      in
                   FStar_Errors.raise_err uu____886
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____894 = implementation_of file_system_map key  in
              (match uu____894 with
               | FStar_Pervasives_Native.None  ->
                   let uu____898 =
                     let uu____903 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____903)
                      in
                   FStar_Errors.raise_err uu____898
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
          let uu____947 = deps_try_find deps fn  in
          match uu____947 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____961) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (add_dependence : dependence_graph -> file_name -> file_name -> unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____1002 to_1 =
          match uu____1002 with
          | (d,color) ->
              let uu____1022 = is_interface to_1  in
              if uu____1022
              then
                let uu____1029 =
                  let uu____1032 =
                    let uu____1033 = lowercase_module_name to_1  in
                    PreferInterface uu____1033  in
                  uu____1032 :: d  in
                (uu____1029, color)
              else
                (let uu____1037 =
                   let uu____1040 =
                     let uu____1041 = lowercase_module_name to_1  in
                     UseImplementation uu____1041  in
                   uu____1040 :: d  in
                 (uu____1037, color))
           in
        let uu____1044 = deps_try_find deps from  in
        match uu____1044 with
        | FStar_Pervasives_Native.None  ->
            let uu____1055 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____1055
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____1071 = add_dep key_deps to_  in
            deps_add_dep deps from uu____1071
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1084 =
       let uu____1085 =
         let uu____1086 =
           let uu____1087 =
             let uu____1090 =
               let uu____1093 = deps_keys graph  in
               FStar_List.unique uu____1093  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1102 =
                      let uu____1107 = deps_try_find graph k  in
                      FStar_Util.must uu____1107  in
                    FStar_Pervasives_Native.fst uu____1102  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1090
              in
           FStar_String.concat "\n" uu____1087  in
         Prims.strcat uu____1086 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1085  in
     FStar_Util.write_file "dep.graph" uu____1084)
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1142  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1159 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1159  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1185 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1185
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1206 =
              let uu____1211 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1211)  in
            FStar_Errors.raise_err uu____1206)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1257 = FStar_Util.smap_try_find map1 key  in
      match uu____1257 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1294 = is_interface full_path  in
          if uu____1294
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1328 = is_interface full_path  in
          if uu____1328
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1355 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1369  ->
          match uu____1369 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1355);
    FStar_List.iter
      (fun f  ->
         let uu____1380 = lowercase_module_name f  in add_entry uu____1380 f)
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
        (let uu____1401 =
           let uu____1404 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1404  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1430 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1430  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1401);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1576 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1576 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1591 = string_of_lid l last1  in
      FStar_String.lowercase uu____1591
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1597 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1597
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1611 =
        let uu____1612 =
          let uu____1613 =
            let uu____1614 =
              let uu____1617 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1617  in
            FStar_Util.must uu____1614  in
          FStar_String.lowercase uu____1613  in
        uu____1612 <> k'  in
      if uu____1611
      then
        let uu____1618 = FStar_Ident.range_of_lid lid  in
        let uu____1619 =
          let uu____1624 =
            let uu____1625 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1625 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1624)  in
        FStar_Errors.log_issue uu____1618 uu____1619
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1632 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1648 = FStar_Options.prims_basename ()  in
      let uu____1649 =
        let uu____1652 = FStar_Options.pervasives_basename ()  in
        let uu____1653 =
          let uu____1656 = FStar_Options.pervasives_native_basename ()  in
          [uu____1656]  in
        uu____1652 :: uu____1653  in
      uu____1648 :: uu____1649  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1691 =
         let uu____1694 = lowercase_module_name full_filename  in
         namespace_of_module uu____1694  in
       match uu____1691 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
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
        let uu____1920 =
          let uu____1921 =
            let uu____1922 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (fun d'  -> d' = d) uu____1922  in
          Prims.op_Negation uu____1921  in
        if uu____1920
        then
          let uu____1996 =
            let uu____1999 = FStar_ST.op_Bang deps1  in d :: uu____1999  in
          FStar_ST.op_Colon_Equals deps1 uu____1996
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2172 = resolve_module_name original_or_working_map key  in
        match uu____2172 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2211 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____2213 = FStar_Options.dep ()  in
                   uu____2213 = (FStar_Pervasives_Native.Some "full"))
                 in
              if uu____2211
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2252 -> false  in
      let record_open_module let_open lid =
        let uu____2266 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2266
        then true
        else
          (if let_open
           then
             (let uu____2269 = FStar_Ident.range_of_lid lid  in
              let uu____2270 =
                let uu____2275 =
                  let uu____2276 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2276  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2275)
                 in
              FStar_Errors.log_issue uu____2269 uu____2270)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2286 = FStar_Ident.range_of_lid lid  in
          let uu____2287 =
            let uu____2292 =
              let uu____2293 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2293
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2292)
             in
          FStar_Errors.log_issue uu____2286 uu____2287
        else ()  in
      let record_open let_open lid =
        let uu____2306 = record_open_module let_open lid  in
        if uu____2306
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2318 =
        match uu____2318 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2325 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2338 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2338  in
        let alias = lowercase_join_longident lid true  in
        let uu____2340 = FStar_Util.smap_try_find original_map alias  in
        match uu____2340 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2394 = FStar_Ident.range_of_lid lid  in
              let uu____2395 =
                let uu____2400 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2400)
                 in
              FStar_Errors.log_issue uu____2394 uu____2395);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2407 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2411 = add_dependence_edge working_map module_name  in
            if uu____2411
            then ()
            else
              (let uu____2413 = FStar_Options.debug_any ()  in
               if uu____2413
               then
                 let uu____2414 = FStar_Ident.range_of_lid lid  in
                 let uu____2415 =
                   let uu____2420 =
                     let uu____2421 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2421
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2420)
                    in
                 FStar_Errors.log_issue uu____2414 uu____2415
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___57_2537 =
         match uu___57_2537 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2546 =
                   let uu____2547 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2547  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2551) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2558 =
                   let uu____2559 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2559  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___58_2568 =
         match uu___58_2568 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2573 = record_module_alias ident lid  in
             if uu____2573
             then
               let uu____2574 =
                 let uu____2575 = lowercase_join_longident lid true  in
                 PreferInterface uu____2575  in
               add_dep deps uu____2574
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2610,patterms) ->
             FStar_List.iter
               (fun uu____2632  ->
                  match uu____2632 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____2641,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____2647,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2649;
               FStar_Parser_AST.mdest = uu____2650;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2652;
               FStar_Parser_AST.mdest = uu____2653;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2655,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2657;
               FStar_Parser_AST.mdest = uu____2658;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2662,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2692  -> match uu____2692 with | (x,docnik) -> x)
                 ts
                in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2705,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2712 -> ()
         | FStar_Parser_AST.Pragma uu____2713 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2749 =
                 let uu____2750 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2750 > (Prims.parse_int "1")  in
               if uu____2749
               then
                 let uu____2796 =
                   let uu____2801 =
                     let uu____2802 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2802
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2801)  in
                 let uu____2803 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____2796 uu____2803
               else ()))
       
       and collect_tycon uu___59_2805 =
         match uu___59_2805 with
         | FStar_Parser_AST.TyconAbstract (uu____2806,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2818,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2832,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2878  ->
                   match uu____2878 with
                   | (uu____2887,t,uu____2889) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2894,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2953  ->
                   match uu____2953 with
                   | (uu____2966,t,uu____2968,uu____2969) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___60_2978 =
         match uu___60_2978 with
         | FStar_Parser_AST.DefineEffect (uu____2979,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2993,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___61_3004 =
         match uu___61_3004 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3005,t);
             FStar_Parser_AST.brange = uu____3007;
             FStar_Parser_AST.blevel = uu____3008;
             FStar_Parser_AST.aqual = uu____3009;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3010,t);
             FStar_Parser_AST.brange = uu____3012;
             FStar_Parser_AST.blevel = uu____3013;
             FStar_Parser_AST.aqual = uu____3014;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3016;
             FStar_Parser_AST.blevel = uu____3017;
             FStar_Parser_AST.aqual = uu____3018;_} -> collect_term t
         | uu____3019 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___62_3021 =
         match uu___62_3021 with
         | FStar_Const.Const_int
             (uu____3022,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3037 =
               let uu____3038 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____3038  in
             add_dep deps uu____3037
         | FStar_Const.Const_char uu____3072 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3106 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3140 -> ()
       
       and collect_term' uu___63_3141 =
         match uu___63_3141 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____3150 =
                 let uu____3151 = FStar_Ident.text_of_id s  in
                 uu____3151 = "@"  in
               if uu____3150
               then
                 let uu____3152 =
                   let uu____3153 =
                     let uu____3154 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____3154
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3153  in
                 collect_term' uu____3152
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3156 -> ()
         | FStar_Parser_AST.Uvar uu____3157 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3160) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3190  ->
                   match uu____3190 with | (t,uu____3196) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3206) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3208,patterms,t) ->
             (FStar_List.iter
                (fun uu____3258  ->
                   match uu____3258 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3287 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3296,t1,t2) ->
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
                (fun uu____3392  ->
                   match uu____3392 with | (uu____3397,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3400) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3456,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3460) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3466) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3472,uu____3473) ->
             collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Quote uu____3475 -> ()
         | FStar_Parser_AST.Antiquote uu____3480 -> ()
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___64_3492 =
         match uu___64_3492 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3493 -> ()
         | FStar_Parser_AST.PatConst uu____3494 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3502 -> ()
         | FStar_Parser_AST.PatName uu____3509 -> ()
         | FStar_Parser_AST.PatTvar uu____3510 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3524) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3543  ->
                  match uu____3543 with | (uu____3548,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3593 =
         match uu____3593 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3611 = FStar_Parser_Driver.parse_file filename  in
       match uu____3611 with
       | (ast,uu____3631) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3646 =
               ((is_interface filename) &&
                  (has_implementation original_map mname))
                 &&
                 (let uu____3648 = FStar_Options.dep ()  in
                  uu____3648 = (FStar_Pervasives_Native.Some "full"))
                in
             if uu____3646
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3688 = FStar_ST.op_Bang deps  in
             let uu____3740 = FStar_ST.op_Bang mo_roots  in
             (uu____3688, uu____3740))))
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____3828 = FStar_Options.find_file fn  in
              match uu____3828 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3831 =
                    let uu____3836 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3836)  in
                  FStar_Errors.raise_err uu____3831
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3846 =
        let uu____3847 = deps_try_find dep_graph file_name  in
        uu____3847 = FStar_Pervasives_Native.None  in
      if uu____3846
      then
        let uu____3864 = collect_one file_system_map file_name  in
        match uu____3864 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____3887 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____3887
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____3892 =
                let uu____3897 = FStar_List.unique deps1  in
                (uu____3897, White)  in
              deps_add_dep dep_graph file_name uu____3892);
             (let uu____3902 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____3902))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec aux cycle filename =
         let uu____3941 =
           let uu____3946 = deps_try_find dep_graph filename  in
           FStar_Util.must uu____3946  in
         match uu____3941 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  ((let uu____3960 =
                      let uu____3965 =
                        FStar_Util.format1
                          "Recursive dependency on module %s\n" filename
                         in
                      (FStar_Errors.Warning_RecursiveDependency, uu____3965)
                       in
                    FStar_Errors.log_issue FStar_Range.dummyRange uu____3960);
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____3971 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3971);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3977 =
                      let uu____3980 = FStar_ST.op_Bang topologically_sorted
                         in
                      filename :: uu____3980  in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3977)))
          in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted  in
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let uu____4138 = topological_dependences_of all_cmd_line_files1  in
      (uu____4138, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____4155  ->
    fun f  ->
      match uu____4155 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____4184  ->
    fun fn  ->
      match uu____4184 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____4202 = FStar_Options.find_file fn  in
            match uu____4202 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____4206 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____4217 = FStar_Options.debug_any ()  in
             if uu____4217
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____4228 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____4228
            then
              let uu____4235 =
                let uu____4240 =
                  let uu____4241 =
                    let uu____4242 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____4242  in
                  digest_of_file1 uu____4241  in
                ("interface", uu____4240)  in
              [uu____4235]
            else []  in
          let binary_deps =
            let uu____4261 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____4261
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____4271 =
                      (is_interface fn2) &&
                        (let uu____4273 = lowercase_module_name fn2  in
                         uu____4273 = module_name)
                       in
                    Prims.op_Negation uu____4271))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____4283 = lowercase_module_name fn11  in
                   let uu____4284 = lowercase_module_name fn2  in
                   FStar_String.compare uu____4283 uu____4284) binary_deps
             in
          let rec hash_deps out uu___65_4311 =
            match uu___65_4311 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4355 =
                    let uu____4362 =
                      let uu____4367 = lowercase_module_name fn2  in
                      let uu____4368 = digest_of_file1 cache_fn  in
                      (uu____4367, uu____4368)  in
                    uu____4362 :: out  in
                  hash_deps uu____4355 deps1
                else
                  ((let uu____4375 = FStar_Options.debug_any ()  in
                    if uu____4375
                    then
                      FStar_Util.print2 "%s: missed digest of file %s\n"
                        cache_file cache_fn
                    else ());
                   FStar_Pervasives_Native.None)
             in
          hash_deps [] binary_deps1
  
let (print_digest :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string)
  =
  fun dig  ->
    let uu____4404 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4423  ->
              match uu____4423 with
              | (m,d) ->
                  let uu____4430 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4430))
       in
    FStar_All.pipe_right uu____4404 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____4437  ->
    match uu____4437 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4457 =
                  let uu____4462 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4462 FStar_Option.get  in
                match uu____4457 with
                | (f_deps,uu____4484) ->
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
  
let (print_full : deps -> unit) =
  fun uu____4498  ->
    match uu____4498 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____4539 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____4539) ||
              (let uu____4543 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____4543)
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
                let uu____4570 =
                  let uu____4573 = FStar_ST.op_Bang order  in ml_file ::
                    uu____4573
                   in
                FStar_ST.op_Colon_Equals order uu____4570
             in
          let rec aux uu___66_4681 =
            match uu___66_4681 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____4699 = deps_try_find deps file_name  in
                      (match uu____4699 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____4710 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____4710
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____4712) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____4723 = should_visit lc_module_name  in
                  if uu____4723
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____4728 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____4728);
                     (let uu____4732 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____4732);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____4740 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____4740)
           in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____4807 =
              let uu____4808 =
                let uu____4811 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____4811  in
              FStar_Option.get uu____4808  in
            FStar_Util.replace_chars uu____4807 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____4826 = output_file ".ml" f  in norm_path uu____4826  in
        let output_krml_file f =
          let uu____4833 = output_file ".krml" f  in norm_path uu____4833  in
        let output_cmx_file f =
          let uu____4840 = output_file ".cmx" f  in norm_path uu____4840  in
        let cache_file f =
          let uu____4847 = cache_file_name f  in norm_path uu____4847  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4890 =
                   let uu____4895 = deps_try_find deps f  in
                   FStar_All.pipe_right uu____4895 FStar_Option.get  in
                 match uu____4890 with
                 | (f_deps,uu____4917) ->
                     let norm_f = norm_path f  in
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps
                        in
                     let files1 = FStar_List.map norm_path files  in
                     let files2 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files1
                        in
                     let files3 = FStar_String.concat "\\\n\t" files2  in
                     ((let uu____4933 = is_interface f  in
                       if uu____4933
                       then
                         let uu____4934 =
                           let uu____4935 =
                             FStar_Options.prepend_cache_dir norm_f  in
                           norm_path uu____4935  in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____4934 norm_f files3
                       else ());
                      (let uu____4938 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4938
                         norm_f files3);
                      (let already_there =
                         let uu____4942 =
                           let uu____4953 =
                             let uu____4954 = output_file ".krml" f  in
                             norm_path uu____4954  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____4953
                            in
                         match uu____4942 with
                         | FStar_Pervasives_Native.Some
                             (uu____4965,already_there,uu____4967) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____4989 =
                          let uu____4990 = output_file ".krml" f  in
                          norm_path uu____4990  in
                        let uu____4991 =
                          let uu____5000 =
                            let uu____5001 = output_file ".exe" f  in
                            norm_path uu____5001  in
                          let uu____5002 =
                            let uu____5005 =
                              let uu____5008 =
                                let uu____5011 =
                                  deps_of
                                    (Mk
                                       (deps, file_system_map,
                                         all_cmd_line_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____5019 = output_file ".krml" x
                                        in
                                     norm_path uu____5019) uu____5011
                                 in
                              FStar_List.append already_there uu____5008  in
                            FStar_List.unique uu____5005  in
                          (uu____5000, uu____5002, false)  in
                        FStar_Util.smap_add transitive_krml uu____4989
                          uu____4991);
                       (let uu____5030 = is_implementation f  in
                        if uu____5030
                        then
                          ((let uu____5032 = output_ml_file f  in
                            let uu____5033 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5032
                              uu____5033);
                           (let cmx_files =
                              let fst_files =
                                FStar_All.pipe_right f_deps
                                  (FStar_List.map
                                     (file_of_dep_aux false file_system_map
                                        all_cmd_line_files))
                                 in
                              let extracted_fst_files =
                                FStar_All.pipe_right fst_files
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____5055 =
                                           lowercase_module_name df  in
                                         let uu____5056 =
                                           lowercase_module_name f  in
                                         uu____5055 <> uu____5056) &&
                                          (let uu____5058 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____5058)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____5064 =
                               let uu____5065 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____5065  in
                             if uu____5064
                             then
                               let uu____5066 = output_cmx_file f  in
                               let uu____5067 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____5066 uu____5067
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____5069 = output_krml_file f  in
                             let uu____5070 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5069
                               uu____5070)))
                        else
                          (let uu____5072 =
                             (let uu____5075 =
                                let uu____5076 = lowercase_module_name f  in
                                has_implementation file_system_map uu____5076
                                 in
                              Prims.op_Negation uu____5075) &&
                               (is_interface f)
                              in
                           if uu____5072
                           then
                             let uu____5077 = output_krml_file f  in
                             let uu____5078 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5077
                               uu____5078
                           else ()))))));
         (let all_fst_files =
            let uu____5083 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____5083
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5109 = FStar_Options.should_extract mname  in
                    if uu____5109
                    then
                      let uu____5110 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____5110
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5126 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____5126));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____5139 =
              let uu____5148 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____5148  in
            match uu____5139 with
            | (exe,deps1,seen) ->
                if seen
                then (exe, deps1)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                   (let deps2 =
                      let uu____5211 =
                        let uu____5214 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____5226 = make_transitive dep1  in
                               match uu____5226 with
                               | (uu____5235,deps2) -> dep1 :: deps2) deps1
                           in
                        FStar_List.flatten uu____5214  in
                      FStar_List.unique uu____5211  in
                    FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                    (exe, deps2)))
             in
          (let uu____5255 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____5274 = make_transitive f  in
                match uu____5274 with
                | (exe,deps1) ->
                    let deps2 =
                      let uu____5288 = FStar_List.unique (f :: deps1)  in
                      FStar_String.concat " " uu____5288  in
                    let wasm =
                      let uu____5292 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____5292 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____5255);
          (let uu____5295 =
             let uu____5296 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5296 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5295);
          (let uu____5306 =
             let uu____5307 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5307 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5306);
          (let uu____5316 =
             let uu____5317 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5317 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5316)))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____5331 = FStar_Options.dep ()  in
    match uu____5331 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____5334 = deps  in
        (match uu____5334 with
         | Mk (deps1,uu____5336,uu____5337) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____5342 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  