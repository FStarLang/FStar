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
let empty_dependences : 'Auu____314 . Prims.unit -> 'Auu____314 Prims.list =
  fun a245  -> (Obj.magic (fun uu____317  -> [])) a245 
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
                      (let uu____828 = lowercase_module_name fn  in
                       key = uu____828)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____836 = interface_of file_system_map key  in
              (match uu____836 with
               | FStar_Pervasives_Native.None  ->
                   let uu____839 = ()  in
                   let uu____840 =
                     let uu____845 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____845)  in
                   FStar_Errors.raise_err uu____840
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____849 =
                (cmd_line_has_impl key) &&
                  (let uu____851 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____851)
                 in
              if uu____849
              then
                let uu____854 = FStar_Options.expose_interfaces ()  in
                (if uu____854
                 then
                   let uu____855 =
                     let uu____856 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____856  in
                   maybe_add_suffix uu____855
                 else
                   (let uu____860 =
                      let uu____865 =
                        let uu____866 =
                          let uu____867 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____867  in
                        let uu____870 =
                          let uu____871 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____871  in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____866 uu____870
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____865)
                       in
                    FStar_Errors.raise_err uu____860))
              else
                (let uu____875 =
                   let uu____876 = interface_of file_system_map key  in
                   FStar_Option.get uu____876  in
                 maybe_add_suffix uu____875)
          | PreferInterface key ->
              let uu____880 = implementation_of file_system_map key  in
              (match uu____880 with
               | FStar_Pervasives_Native.None  ->
                   let uu____883 = ()  in
                   let uu____884 =
                     let uu____889 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____889)
                      in
                   FStar_Errors.raise_err uu____884
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____892 = implementation_of file_system_map key  in
              (match uu____892 with
               | FStar_Pervasives_Native.None  ->
                   let uu____895 = ()  in
                   let uu____896 =
                     let uu____901 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____901)
                      in
                   FStar_Errors.raise_err uu____896
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
          let uu____945 = deps_try_find deps fn  in
          match uu____945 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____959) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (add_dependence : dependence_graph -> file_name -> file_name -> unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____998 to_1 =
          match uu____998 with
          | (d,color) ->
              let uu____1018 = is_interface to_1  in
              if uu____1018
              then
                let uu____1025 =
                  let uu____1028 =
                    let uu____1029 = lowercase_module_name to_1  in
                    PreferInterface uu____1029  in
                  uu____1028 :: d  in
                (uu____1025, color)
              else
                (let uu____1033 =
                   let uu____1036 =
                     let uu____1037 = lowercase_module_name to_1  in
                     UseImplementation uu____1037  in
                   uu____1036 :: d  in
                 (uu____1033, color))
           in
        let uu____1040 = deps_try_find deps from  in
        match uu____1040 with
        | FStar_Pervasives_Native.None  ->
            let uu____1051 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____1051
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____1067 = add_dep key_deps to_  in
            deps_add_dep deps from uu____1067
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    let uu____1077 =
      FStar_Util.print_endline
        "A DOT-format graph has been dumped in the current directory as dep.graph"
       in
    let uu____1078 =
      FStar_Util.print_endline
        "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph"
       in
    let uu____1079 =
      FStar_Util.print_endline
        "Hint: cat dep.graph | grep -v _ | grep -v prims"
       in
    let uu____1080 =
      let uu____1081 =
        let uu____1082 =
          let uu____1083 =
            let uu____1086 =
              let uu____1089 = deps_keys graph  in
              FStar_List.unique uu____1089  in
            FStar_List.collect
              (fun k  ->
                 let deps =
                   let uu____1098 =
                     let uu____1103 = deps_try_find graph k  in
                     FStar_Util.must uu____1103  in
                   FStar_Pervasives_Native.fst uu____1098  in
                 let r s = FStar_Util.replace_char s 46 95  in
                 let print7 dep1 =
                   FStar_Util.format2 " %s -> %s" (r k)
                     (r (module_name_of_dep dep1))
                    in
                 FStar_List.map print7 deps) uu____1086
             in
          FStar_String.concat "\n" uu____1083  in
        Prims.strcat uu____1082 "\n}\n"  in
      Prims.strcat "digraph {\n" uu____1081  in
    FStar_Util.write_file "dep.graph" uu____1080
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1136  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1153 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1153  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1179 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1179
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1200 =
              let uu____1205 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1205)  in
            FStar_Errors.raise_err uu____1200)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1249 = FStar_Util.smap_try_find map1 key  in
      match uu____1249 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1286 = is_interface full_path  in
          if uu____1286
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1320 = is_interface full_path  in
          if uu____1320
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    let uu____1346 =
      let uu____1347 = build_inclusion_candidates_list ()  in
      FStar_List.iter
        (fun uu____1361  ->
           match uu____1361 with
           | (longname,full_path) ->
               add_entry (FStar_String.lowercase longname) full_path)
        uu____1347
       in
    let uu____1368 =
      FStar_List.iter
        (fun f  ->
           let uu____1372 = lowercase_module_name f  in
           add_entry uu____1372 f) filenames
       in
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
        let uu____1392 =
          let uu____1393 =
            let uu____1396 = FStar_Util.smap_keys original_map  in
            FStar_List.unique uu____1396  in
          FStar_List.iter
            (fun k  ->
               if FStar_Util.starts_with k prefix2
               then
                 let suffix =
                   FStar_String.substring k (FStar_String.length prefix2)
                     ((FStar_String.length k) - (FStar_String.length prefix2))
                    in
                 let filename =
                   let uu____1422 = FStar_Util.smap_try_find original_map k
                      in
                   FStar_Util.must uu____1422  in
                 let uu____1449 =
                   FStar_Util.smap_add working_map suffix filename  in
                 FStar_ST.op_Colon_Equals found true
               else ()) uu____1393
           in
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1568 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1568 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1583 = string_of_lid l last1  in
      FStar_String.lowercase uu____1583
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1589 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1589
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1603 =
        let uu____1604 =
          let uu____1605 =
            let uu____1606 =
              let uu____1609 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1609  in
            FStar_Util.must uu____1606  in
          FStar_String.lowercase uu____1605  in
        uu____1604 <> k'  in
      if uu____1603
      then
        let uu____1610 = FStar_Ident.range_of_lid lid  in
        let uu____1611 =
          let uu____1616 =
            let uu____1617 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1617 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1616)  in
        FStar_Errors.log_issue uu____1610 uu____1611
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1624 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1640 = FStar_Options.prims_basename ()  in
      let uu____1641 =
        let uu____1644 = FStar_Options.pervasives_basename ()  in
        let uu____1645 =
          let uu____1648 = FStar_Options.pervasives_native_basename ()  in
          [uu____1648]  in
        uu____1644 :: uu____1645  in
      uu____1640 :: uu____1641  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1683 =
         let uu____1686 = lowercase_module_name full_filename  in
         namespace_of_module uu____1686  in
       match uu____1683 with
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
        let uu____1889 =
          let uu____1890 =
            let uu____1891 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (fun d'  -> d' = d) uu____1891  in
          Prims.op_Negation uu____1890  in
        if uu____1889
        then
          let uu____1965 =
            let uu____1968 = FStar_ST.op_Bang deps1  in d :: uu____1968  in
          FStar_ST.op_Colon_Equals deps1 uu____1965
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2139 = resolve_module_name original_or_working_map key  in
        match uu____2139 with
        | FStar_Pervasives_Native.Some module_name ->
            let uu____2143 = add_dep deps (PreferInterface module_name)  in
            let uu____2177 =
              let uu____2178 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____2180 = FStar_Options.dep ()  in
                   uu____2180 = (FStar_Pervasives_Native.Some "full"))
                 in
              if uu____2178
              then add_dep mo_roots (UseImplementation module_name)
              else ()  in
            true
        | uu____2219 -> false  in
      let record_open_module let_open lid =
        let uu____2231 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2231
        then true
        else
          (let uu____2233 =
             if let_open
             then
               let uu____2234 = FStar_Ident.range_of_lid lid  in
               let uu____2235 =
                 let uu____2240 =
                   let uu____2241 = string_of_lid lid true  in
                   FStar_Util.format1 "Module not found: %s" uu____2241  in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____2240)
                  in
               FStar_Errors.log_issue uu____2234 uu____2235
             else ()  in
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2250 = FStar_Ident.range_of_lid lid  in
          let uu____2251 =
            let uu____2256 =
              let uu____2257 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2257
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2256)
             in
          FStar_Errors.log_issue uu____2250 uu____2251
        else ()  in
      let record_open let_open lid =
        let uu____2268 = record_open_module let_open lid  in
        if uu____2268
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2279 =
        match uu____2279 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2286 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2297 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2297  in
        let alias = lowercase_join_longident lid true  in
        let uu____2299 = FStar_Util.smap_try_find original_map alias  in
        match uu____2299 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            let uu____2335 =
              FStar_Util.smap_add working_map key deps_of_aliased_module  in
            true
        | FStar_Pervasives_Native.None  ->
            let uu____2352 =
              let uu____2353 = FStar_Ident.range_of_lid lid  in
              let uu____2354 =
                let uu____2359 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2359)
                 in
              FStar_Errors.log_issue uu____2353 uu____2354  in
            false
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2365 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2369 = add_dependence_edge working_map module_name  in
            if uu____2369
            then ()
            else
              (let uu____2371 = FStar_Options.debug_any ()  in
               if uu____2371
               then
                 let uu____2372 = FStar_Ident.range_of_lid lid  in
                 let uu____2373 =
                   let uu____2378 =
                     let uu____2379 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2379
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2378)
                    in
                 FStar_Errors.log_issue uu____2372 uu____2373
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      let uu____2388 =
        FStar_List.iter record_open_module_or_namespace auto_open  in
      let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
      let rec collect_module uu___57_2480 =
        match uu___57_2480 with
        | FStar_Parser_AST.Module (lid,decls) ->
            let uu____2487 =
              check_module_declaration_against_filename lid filename  in
            let uu____2488 =
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                let uu____2489 =
                  let uu____2490 = namespace_of_lid lid  in
                  enter_namespace original_map working_map uu____2490  in
                ()
              else ()  in
            collect_decls decls
        | FStar_Parser_AST.Interface (lid,decls,uu____2494) ->
            let uu____2499 =
              check_module_declaration_against_filename lid filename  in
            let uu____2500 =
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                let uu____2501 =
                  let uu____2502 = namespace_of_lid lid  in
                  enter_namespace original_map working_map uu____2502  in
                ()
              else ()  in
            collect_decls decls
      
      and collect_decls decls =
        FStar_List.iter
          (fun x  ->
             let uu____2510 = collect_decl x.FStar_Parser_AST.d  in
             FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
      
      and collect_decl uu___58_2511 =
        match uu___58_2511 with
        | FStar_Parser_AST.Include lid -> record_open false lid
        | FStar_Parser_AST.Open lid -> record_open false lid
        | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
            let uu____2516 = record_module_alias ident lid  in
            if uu____2516
            then
              let uu____2517 =
                let uu____2518 = lowercase_join_longident lid true  in
                PreferInterface uu____2518  in
              add_dep deps uu____2517
            else ()
        | FStar_Parser_AST.TopLevelLet (uu____2553,patterms) ->
            FStar_List.iter
              (fun uu____2575  ->
                 match uu____2575 with
                 | (pat,t) ->
                     let uu____2582 = collect_pattern pat  in collect_term t)
              patterms
        | FStar_Parser_AST.Main t -> collect_term t
        | FStar_Parser_AST.Splice (uu____2584,t) -> collect_term t
        | FStar_Parser_AST.Assume (uu____2590,t) -> collect_term t
        | FStar_Parser_AST.SubEffect
            { FStar_Parser_AST.msource = uu____2592;
              FStar_Parser_AST.mdest = uu____2593;
              FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
            -> collect_term t
        | FStar_Parser_AST.SubEffect
            { FStar_Parser_AST.msource = uu____2595;
              FStar_Parser_AST.mdest = uu____2596;
              FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
            -> collect_term t
        | FStar_Parser_AST.Val (uu____2598,t) -> collect_term t
        | FStar_Parser_AST.SubEffect
            { FStar_Parser_AST.msource = uu____2600;
              FStar_Parser_AST.mdest = uu____2601;
              FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                (t0,t1);_}
            -> let uu____2604 = collect_term t0  in collect_term t1
        | FStar_Parser_AST.Tycon (uu____2605,ts) ->
            let ts1 =
              FStar_List.map
                (fun uu____2635  -> match uu____2635 with | (x,docnik) -> x)
                ts
               in
            FStar_List.iter collect_tycon ts1
        | FStar_Parser_AST.Exception (uu____2648,t) ->
            FStar_Util.iter_opt t collect_term
        | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
        | FStar_Parser_AST.Fsdoc uu____2655 -> ()
        | FStar_Parser_AST.Pragma uu____2656 -> ()
        | FStar_Parser_AST.TopLevelModule lid ->
            let uu____2658 = FStar_Util.incr num_of_toplevelmods  in
            let uu____2692 =
              let uu____2693 = FStar_ST.op_Bang num_of_toplevelmods  in
              uu____2693 > (Prims.parse_int "1")  in
            if uu____2692
            then
              let uu____2739 =
                let uu____2744 =
                  let uu____2745 = string_of_lid lid true  in
                  FStar_Util.format1
                    "Automatic dependency analysis demands one module per file (module %s not supported)"
                    uu____2745
                   in
                (FStar_Errors.Fatal_OneModulePerFile, uu____2744)  in
              let uu____2746 = FStar_Ident.range_of_lid lid  in
              FStar_Errors.raise_error uu____2739 uu____2746
            else ()
      
      and collect_tycon uu___59_2748 =
        match uu___59_2748 with
        | FStar_Parser_AST.TyconAbstract (uu____2749,binders,k) ->
            let uu____2760 = collect_binders binders  in
            FStar_Util.iter_opt k collect_term
        | FStar_Parser_AST.TyconAbbrev (uu____2761,binders,k,t) ->
            let uu____2773 = collect_binders binders  in
            let uu____2774 = FStar_Util.iter_opt k collect_term  in
            collect_term t
        | FStar_Parser_AST.TyconRecord (uu____2775,binders,k,identterms) ->
            let uu____2807 = collect_binders binders  in
            let uu____2808 = FStar_Util.iter_opt k collect_term  in
            FStar_List.iter
              (fun uu____2821  ->
                 match uu____2821 with
                 | (uu____2830,t,uu____2832) -> collect_term t) identterms
        | FStar_Parser_AST.TyconVariant (uu____2837,binders,k,identterms) ->
            let uu____2877 = collect_binders binders  in
            let uu____2878 = FStar_Util.iter_opt k collect_term  in
            FStar_List.iter
              (fun uu____2896  ->
                 match uu____2896 with
                 | (uu____2909,t,uu____2911,uu____2912) ->
                     FStar_Util.iter_opt t collect_term) identterms
      
      and collect_effect_decl uu___60_2921 =
        match uu___60_2921 with
        | FStar_Parser_AST.DefineEffect (uu____2922,binders,t,decls) ->
            let uu____2934 = collect_binders binders  in
            let uu____2935 = collect_term t  in collect_decls decls
        | FStar_Parser_AST.RedefineEffect (uu____2936,binders,t) ->
            let uu____2943 = collect_binders binders  in collect_term t
      
      and collect_binders binders = FStar_List.iter collect_binder binders
      
      and collect_binder uu___61_2947 =
        match uu___61_2947 with
        | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2948,t);
            FStar_Parser_AST.brange = uu____2950;
            FStar_Parser_AST.blevel = uu____2951;
            FStar_Parser_AST.aqual = uu____2952;_} -> collect_term t
        | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2953,t);
            FStar_Parser_AST.brange = uu____2955;
            FStar_Parser_AST.blevel = uu____2956;
            FStar_Parser_AST.aqual = uu____2957;_} -> collect_term t
        | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
            FStar_Parser_AST.brange = uu____2959;
            FStar_Parser_AST.blevel = uu____2960;
            FStar_Parser_AST.aqual = uu____2961;_} -> collect_term t
        | uu____2962 -> ()
      
      and collect_term t = collect_term' t.FStar_Parser_AST.tm
      
      and collect_constant uu___62_2964 =
        match uu___62_2964 with
        | FStar_Const.Const_int
            (uu____2965,FStar_Pervasives_Native.Some (signedness,width)) ->
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
            let uu____2980 =
              let uu____2981 = FStar_Util.format2 "fstar.%sint%s" u w  in
              PreferInterface uu____2981  in
            add_dep deps uu____2980
        | FStar_Const.Const_char uu____3015 ->
            add_dep deps (PreferInterface "fstar.char")
        | FStar_Const.Const_float uu____3049 ->
            add_dep deps (PreferInterface "fstar.float")
        | uu____3083 -> ()
      
      and collect_term' uu___63_3084 =
        match uu___63_3084 with
        | FStar_Parser_AST.Wild  -> ()
        | FStar_Parser_AST.Const c -> collect_constant c
        | FStar_Parser_AST.Op (s,ts) ->
            let uu____3092 =
              let uu____3093 =
                let uu____3094 = FStar_Ident.text_of_id s  in
                uu____3094 = "@"  in
              if uu____3093
              then
                let uu____3095 =
                  let uu____3096 =
                    let uu____3097 =
                      FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                       in
                    FStar_Ident.lid_of_path uu____3097 FStar_Range.dummyRange
                     in
                  FStar_Parser_AST.Name uu____3096  in
                collect_term' uu____3095
              else ()  in
            FStar_List.iter collect_term ts
        | FStar_Parser_AST.Tvar uu____3099 -> ()
        | FStar_Parser_AST.Uvar uu____3100 -> ()
        | FStar_Parser_AST.Var lid -> record_lid lid
        | FStar_Parser_AST.Projector (lid,uu____3103) -> record_lid lid
        | FStar_Parser_AST.Discrim lid -> record_lid lid
        | FStar_Parser_AST.Name lid -> record_lid lid
        | FStar_Parser_AST.Construct (lid,termimps) ->
            let uu____3120 =
              if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ()  in
            FStar_List.iter
              (fun uu____3133  ->
                 match uu____3133 with | (t,uu____3139) -> collect_term t)
              termimps
        | FStar_Parser_AST.Abs (pats,t) ->
            let uu____3146 = collect_patterns pats  in collect_term t
        | FStar_Parser_AST.App (t1,t2,uu____3149) ->
            let uu____3150 = collect_term t1  in collect_term t2
        | FStar_Parser_AST.Let (uu____3151,patterms,t) ->
            let uu____3182 =
              FStar_List.iter
                (fun uu____3201  ->
                   match uu____3201 with
                   | (attrs_opt,(pat,t1)) ->
                       let uu____3229 =
                         let uu____3230 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ()  in
                       let uu____3235 = collect_pattern pat  in
                       collect_term t1) patterms
               in
            collect_term t
        | FStar_Parser_AST.LetOpen (lid,t) ->
            let uu____3238 = record_open true lid  in collect_term t
        | FStar_Parser_AST.Bind (uu____3239,t1,t2) ->
            let uu____3242 = collect_term t1  in collect_term t2
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3245 = collect_term t1  in collect_term t2
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let uu____3249 = collect_term t1  in
            let uu____3250 = collect_term t2  in collect_term t3
        | FStar_Parser_AST.Match (t,bs) ->
            let uu____3273 = collect_term t  in collect_branches bs
        | FStar_Parser_AST.TryWith (t,bs) ->
            let uu____3296 = collect_term t  in collect_branches bs
        | FStar_Parser_AST.Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
            let uu____3301 = collect_term t1  in collect_term t2
        | FStar_Parser_AST.Ascribed (t1,t2,FStar_Pervasives_Native.Some tac)
            ->
            let uu____3307 = collect_term t1  in
            let uu____3308 = collect_term t2  in collect_term tac
        | FStar_Parser_AST.Record (t,idterms) ->
            let uu____3327 = FStar_Util.iter_opt t collect_term  in
            FStar_List.iter
              (fun uu____3335  ->
                 match uu____3335 with | (uu____3340,t1) -> collect_term t1)
              idterms
        | FStar_Parser_AST.Project (t,uu____3343) -> collect_term t
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3350 = collect_binders binders  in collect_term t
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3357 = collect_binders binders  in collect_term t
        | FStar_Parser_AST.QForall (binders,ts,t) ->
            let uu____3373 = collect_binders binders  in
            let uu____3374 =
              FStar_List.iter (FStar_List.iter collect_term) ts  in
            collect_term t
        | FStar_Parser_AST.QExists (binders,ts,t) ->
            let uu____3392 = collect_binders binders  in
            let uu____3393 =
              FStar_List.iter (FStar_List.iter collect_term) ts  in
            collect_term t
        | FStar_Parser_AST.Refine (binder,t) ->
            let uu____3398 = collect_binder binder  in collect_term t
        | FStar_Parser_AST.NamedTyp (uu____3399,t) -> collect_term t
        | FStar_Parser_AST.Paren t -> collect_term t
        | FStar_Parser_AST.Requires (t,uu____3403) -> collect_term t
        | FStar_Parser_AST.Ensures (t,uu____3409) -> collect_term t
        | FStar_Parser_AST.Labeled (t,uu____3415,uu____3416) ->
            collect_term t
        | FStar_Parser_AST.VQuote t -> collect_term t
        | FStar_Parser_AST.Quote uu____3418 -> ()
        | FStar_Parser_AST.Antiquote uu____3423 -> ()
        | FStar_Parser_AST.Attributes cattributes ->
            FStar_List.iter collect_term cattributes
      
      and collect_patterns ps = FStar_List.iter collect_pattern ps
      
      and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
      
      and collect_pattern' uu___64_3435 =
        match uu___64_3435 with
        | FStar_Parser_AST.PatWild  -> ()
        | FStar_Parser_AST.PatOp uu____3436 -> ()
        | FStar_Parser_AST.PatConst uu____3437 -> ()
        | FStar_Parser_AST.PatApp (p,ps) ->
            let uu____3444 = collect_pattern p  in collect_patterns ps
        | FStar_Parser_AST.PatVar uu____3445 -> ()
        | FStar_Parser_AST.PatName uu____3452 -> ()
        | FStar_Parser_AST.PatTvar uu____3453 -> ()
        | FStar_Parser_AST.PatList ps -> collect_patterns ps
        | FStar_Parser_AST.PatOr ps -> collect_patterns ps
        | FStar_Parser_AST.PatTuple (ps,uu____3467) -> collect_patterns ps
        | FStar_Parser_AST.PatRecord lidpats ->
            FStar_List.iter
              (fun uu____3486  ->
                 match uu____3486 with | (uu____3491,p) -> collect_pattern p)
              lidpats
        | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
            -> let uu____3503 = collect_pattern p  in collect_term t
        | FStar_Parser_AST.PatAscribed
            (p,(t,FStar_Pervasives_Native.Some tac)) ->
            let uu____3515 = collect_pattern p  in
            let uu____3516 = collect_term t  in collect_term tac
      
      and collect_branches bs = FStar_List.iter collect_branch bs
      
      and collect_branch uu____3536 =
        match uu____3536 with
        | (pat,t1,t2) ->
            let uu____3552 = collect_pattern pat  in
            let uu____3553 = FStar_Util.iter_opt t1 collect_term  in
            collect_term t2
       in
      let uu____3554 = FStar_Parser_Driver.parse_file filename  in
      match uu____3554 with
      | (ast,uu____3574) ->
          let mname = lowercase_module_name filename  in
          let uu____3588 =
            let uu____3589 =
              ((is_interface filename) &&
                 (has_implementation original_map mname))
                &&
                (let uu____3591 = FStar_Options.dep ()  in
                 uu____3591 = (FStar_Pervasives_Native.Some "full"))
               in
            if uu____3589
            then add_dep mo_roots (UseImplementation mname)
            else ()  in
          let uu____3630 = collect_module ast  in
          let uu____3631 = FStar_ST.op_Bang deps  in
          let uu____3683 = FStar_ST.op_Bang mo_roots  in
          (uu____3631, uu____3683)
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____3771 = FStar_Options.find_file fn  in
              match uu____3771 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3774 =
                    let uu____3779 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3779)  in
                  FStar_Errors.raise_err uu____3774
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3788 =
        let uu____3789 = deps_try_find dep_graph file_name  in
        uu____3789 = FStar_Pervasives_Native.None  in
      if uu____3788
      then
        let uu____3806 = collect_one file_system_map file_name  in
        match uu____3806 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____3829 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____3829
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            let uu____3833 =
              let uu____3834 =
                let uu____3839 = FStar_List.unique deps1  in
                (uu____3839, White)  in
              deps_add_dep dep_graph file_name uu____3834  in
            let uu____3844 =
              FStar_List.map
                (file_of_dep file_system_map all_cmd_line_files1)
                (FStar_List.append deps1 mo_roots)
               in
            FStar_List.iter discover_one uu____3844
      else ()  in
    let uu____3848 = FStar_List.iter discover_one all_cmd_line_files1  in
    let topological_dependences_of all_command_line_files =
      let topologically_sorted = FStar_Util.mk_ref []  in
      let rec aux cycle filename =
        let uu____3880 =
          let uu____3885 = deps_try_find dep_graph filename  in
          FStar_Util.must uu____3885  in
        match uu____3880 with
        | (direct_deps,color) ->
            (match color with
             | Gray  ->
                 let uu____3898 =
                   let uu____3899 =
                     let uu____3904 =
                       FStar_Util.format1
                         "Recursive dependency on module %s\n" filename
                        in
                     (FStar_Errors.Warning_RecursiveDependency, uu____3904)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____3899
                    in
                 let uu____3905 =
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle)
                    in
                 let uu____3906 = print_graph dep_graph  in
                 let uu____3907 = FStar_Util.print_string "\n"  in
                 FStar_All.exit (Prims.parse_int "1")
             | Black  -> ()
             | White  ->
                 let uu____3908 =
                   deps_add_dep dep_graph filename (direct_deps, Gray)  in
                 let uu____3909 =
                   let uu____3910 =
                     dependences_of file_system_map dep_graph
                       all_command_line_files filename
                      in
                   FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3910
                    in
                 let uu____3915 =
                   deps_add_dep dep_graph filename (direct_deps, Black)  in
                 let uu____3916 =
                   let uu____3919 = FStar_ST.op_Bang topologically_sorted  in
                   filename :: uu____3919  in
                 FStar_ST.op_Colon_Equals topologically_sorted uu____3916)
         in
      let uu____4020 = FStar_List.iter (aux []) all_command_line_files  in
      FStar_ST.op_Bang topologically_sorted  in
    let uu____4070 =
      FStar_All.pipe_right all_cmd_line_files1
        (FStar_List.iter
           (fun f  ->
              let m = lowercase_module_name f  in
              FStar_Options.add_verify_module m))
       in
    let uu____4077 = topological_dependences_of all_cmd_line_files1  in
    (uu____4077, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____4094  ->
    fun f  ->
      match uu____4094 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____4123  ->
    fun fn  ->
      match uu____4123 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____4141 = FStar_Options.find_file fn  in
            match uu____4141 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____4145 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            let uu____4154 =
              let uu____4155 = FStar_Options.debug_any ()  in
              if uu____4155
              then
                FStar_Util.print2 "%s: contains digest of %s\n" cache_file
                  fn2
              else ()  in
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____4166 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____4166
            then
              let uu____4173 =
                let uu____4178 =
                  let uu____4179 =
                    let uu____4180 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____4180  in
                  digest_of_file1 uu____4179  in
                ("interface", uu____4178)  in
              [uu____4173]
            else []  in
          let binary_deps =
            let uu____4199 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____4199
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____4209 =
                      (is_interface fn2) &&
                        (let uu____4211 = lowercase_module_name fn2  in
                         uu____4211 = module_name)
                       in
                    Prims.op_Negation uu____4209))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____4221 = lowercase_module_name fn11  in
                   let uu____4222 = lowercase_module_name fn2  in
                   FStar_String.compare uu____4221 uu____4222) binary_deps
             in
          let rec hash_deps out uu___65_4247 =
            match uu___65_4247 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4291 =
                    let uu____4298 =
                      let uu____4303 = lowercase_module_name fn2  in
                      let uu____4304 = digest_of_file1 cache_fn  in
                      (uu____4303, uu____4304)  in
                    uu____4298 :: out  in
                  hash_deps uu____4291 deps1
                else
                  (let uu____4310 =
                     let uu____4311 = FStar_Options.debug_any ()  in
                     if uu____4311
                     then
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file cache_fn
                     else ()  in
                   FStar_Pervasives_Native.None)
             in
          hash_deps [] binary_deps1
  
let (print_digest :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string)
  =
  fun dig  ->
    let uu____4340 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4359  ->
              match uu____4359 with
              | (m,d) ->
                  let uu____4366 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4366))
       in
    FStar_All.pipe_right uu____4340 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____4373  ->
    match uu____4373 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4393 =
                  let uu____4398 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4398 FStar_Option.get  in
                match uu____4393 with
                | (f_deps,uu____4420) ->
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
  fun uu____4434  ->
    match uu____4434 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____4473 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____4473) ||
              (let uu____4477 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____4477)
             in
          let mark_visiting lc_module_name =
            let ml_file_opt =
              FStar_Util.smap_try_find remaining_output_files lc_module_name
               in
            let uu____4490 =
              FStar_Util.smap_remove remaining_output_files lc_module_name
               in
            let uu____4491 =
              FStar_Util.smap_add visited_other_modules lc_module_name true
               in
            ml_file_opt  in
          let emit_output_file_opt ml_file_opt =
            match ml_file_opt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some ml_file ->
                let uu____4502 =
                  let uu____4505 = FStar_ST.op_Bang order  in ml_file ::
                    uu____4505
                   in
                FStar_ST.op_Colon_Equals order uu____4502
             in
          let rec aux uu___66_4612 =
            match uu___66_4612 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____4629 = deps_try_find deps file_name  in
                      (match uu____4629 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____4640 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____4640
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____4642) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                let uu____4652 =
                  let uu____4653 = should_visit lc_module_name  in
                  if uu____4653
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    let uu____4657 =
                      let uu____4658 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____4658  in
                    let uu____4661 =
                      let uu____4662 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____4662  in
                    emit_output_file_opt ml_file_opt
                  else ()  in
                aux modules_to_extract
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          let uu____4669 = aux all_extracted_modules  in
          let uu____4670 = FStar_ST.op_Bang order  in
          FStar_List.rev uu____4670  in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____4735 =
              let uu____4736 =
                let uu____4739 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____4739  in
              FStar_Option.get uu____4736  in
            FStar_Util.replace_chars uu____4735 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____4752 = output_file ".ml" f  in norm_path uu____4752  in
        let output_krml_file f =
          let uu____4758 = output_file ".krml" f  in norm_path uu____4758  in
        let output_cmx_file f =
          let uu____4764 = output_file ".cmx" f  in norm_path uu____4764  in
        let cache_file f =
          let uu____4770 = cache_file_name f  in norm_path uu____4770  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        let uu____4790 =
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun f  ->
                  let uu____4812 =
                    let uu____4817 = deps_try_find deps f  in
                    FStar_All.pipe_right uu____4817 FStar_Option.get  in
                  match uu____4812 with
                  | (f_deps,uu____4839) ->
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
                      let uu____4854 =
                        let uu____4855 = is_interface f  in
                        if uu____4855
                        then
                          let uu____4856 =
                            let uu____4857 =
                              FStar_Options.prepend_cache_dir norm_f  in
                            norm_path uu____4857  in
                          FStar_Util.print3
                            "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                            uu____4856 norm_f files3
                        else ()  in
                      let uu____4859 =
                        let uu____4860 = cache_file f  in
                        FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4860
                          norm_f files3
                         in
                      let uu____4861 =
                        let uu____4862 =
                          let uu____4863 = output_file ".krml" f  in
                          norm_path uu____4863  in
                        let uu____4864 =
                          let uu____4873 =
                            let uu____4874 = output_file ".exe" f  in
                            norm_path uu____4874  in
                          let uu____4875 =
                            let uu____4878 =
                              deps_of
                                (Mk
                                   (deps, file_system_map,
                                     all_cmd_line_files)) f
                               in
                            FStar_List.map
                              (fun x  ->
                                 let uu____4886 = output_file ".krml" x  in
                                 norm_path uu____4886) uu____4878
                             in
                          (uu____4873, uu____4875, false)  in
                        FStar_Util.smap_add transitive_krml uu____4862
                          uu____4864
                         in
                      let uu____4897 = is_implementation f  in
                      if uu____4897
                      then
                        let uu____4898 =
                          let uu____4899 = output_ml_file f  in
                          let uu____4900 = cache_file f  in
                          FStar_Util.print2 "%s: %s\n\n" uu____4899
                            uu____4900
                           in
                        let cmx_files =
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
                                    (let uu____4922 =
                                       lowercase_module_name df  in
                                     let uu____4923 = lowercase_module_name f
                                        in
                                     uu____4922 <> uu____4923) &&
                                      (let uu____4925 =
                                         lowercase_module_name df  in
                                       FStar_Options.should_extract
                                         uu____4925)))
                             in
                          FStar_All.pipe_right extracted_fst_files
                            (FStar_List.map output_cmx_file)
                           in
                        let uu____4930 =
                          let uu____4931 =
                            let uu____4932 = lowercase_module_name f  in
                            FStar_Options.should_extract uu____4932  in
                          if uu____4931
                          then
                            let uu____4933 = output_cmx_file f  in
                            let uu____4934 = output_ml_file f  in
                            FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                              uu____4933 uu____4934
                              (FStar_String.concat "\\\n\t" cmx_files)
                          else ()  in
                        let uu____4936 = output_krml_file f  in
                        let uu____4937 = cache_file f  in
                        FStar_Util.print2 "%s: %s\n\n" uu____4936 uu____4937
                      else
                        (let uu____4939 =
                           (let uu____4942 =
                              let uu____4943 = lowercase_module_name f  in
                              has_implementation file_system_map uu____4943
                               in
                            Prims.op_Negation uu____4942) && (is_interface f)
                            in
                         if uu____4939
                         then
                           let uu____4944 = output_krml_file f  in
                           let uu____4945 = cache_file f  in
                           FStar_Util.print2 "%s: %s\n\n" uu____4944
                             uu____4945
                         else ())))
           in
        let all_fst_files =
          let uu____4950 =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation)
             in
          FStar_All.pipe_right uu____4950
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          let uu____4967 =
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____4976 = FStar_Options.should_extract mname  in
                    if uu____4976
                    then
                      let uu____4977 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____4977
                    else ()))
             in
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          let uu____4985 =
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____4993 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____4993))
             in
          sort_output_files krml_file_map  in
        let rec make_transitive f =
          let uu____5005 =
            let uu____5014 = FStar_Util.smap_try_find transitive_krml f  in
            FStar_Util.must uu____5014  in
          match uu____5005 with
          | (exe,deps1,seen) ->
              if seen
              then (exe, deps1)
              else
                (let uu____5063 =
                   FStar_Util.smap_add transitive_krml f (exe, deps1, true)
                    in
                 let deps2 =
                   let uu____5077 =
                     let uu____5080 =
                       FStar_List.map
                         (fun dep1  ->
                            let uu____5092 = make_transitive dep1  in
                            match uu____5092 with
                            | (uu____5101,deps2) -> dep1 :: deps2) deps1
                        in
                     FStar_List.flatten uu____5080  in
                   FStar_List.unique uu____5077  in
                 let uu____5107 =
                   FStar_Util.smap_add transitive_krml f (exe, deps2, true)
                    in
                 (exe, deps2))
           in
        let uu____5120 =
          let uu____5121 = FStar_Util.smap_keys transitive_krml  in
          FStar_List.iter
            (fun f  ->
               let uu____5140 = make_transitive f  in
               match uu____5140 with
               | (exe,deps1) ->
                   let deps2 =
                     let uu____5154 = FStar_List.unique (f :: deps1)  in
                     FStar_String.concat " " uu____5154  in
                   let wasm =
                     let uu____5158 =
                       FStar_Util.substring exe (Prims.parse_int "0")
                         ((FStar_String.length exe) - (Prims.parse_int "4"))
                        in
                     Prims.strcat uu____5158 ".wasm"  in
                   let uu____5159 = FStar_Util.print2 "%s: %s\n\n" exe deps2
                      in
                   FStar_Util.print2 "%s: %s\n\n" wasm deps2) uu____5121
           in
        let uu____5160 =
          let uu____5161 =
            let uu____5162 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____5162 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5161  in
        let uu____5171 =
          let uu____5172 =
            let uu____5173 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____5173 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5172  in
        let uu____5182 =
          let uu____5183 =
            FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
             in
          FStar_All.pipe_right uu____5183 (FStar_String.concat " \\\n\t")  in
        FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5182
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____5197 = FStar_Options.dep ()  in
    match uu____5197 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____5200 = deps  in
        (match uu____5200 with
         | Mk (deps1,uu____5202,uu____5203) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____5208 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  