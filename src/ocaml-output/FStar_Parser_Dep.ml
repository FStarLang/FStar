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
  fun uu___105_177  ->
    match uu___105_177 with
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
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____277 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____291 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____305 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
type dependences = dependence Prims.list
let empty_dependences : 'Auu____317 . unit -> 'Auu____317 Prims.list =
  fun uu____320  -> [] 
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
  fun uu____423  ->
    fun k  -> match uu____423 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun uu____458  ->
    fun k  ->
      fun v1  -> match uu____458 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____482  -> match uu____482 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____500  ->
    let uu____501 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____501
  
let (empty_deps : deps) =
  let uu____512 =
    let uu____521 = deps_empty ()  in
    let uu____522 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____521, uu____522, [])  in
  Mk uu____512 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___106_537  ->
    match uu___106_537 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____555 = FStar_Util.smap_try_find file_system_map key  in
      match uu____555 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____577) ->
          let uu____592 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____592
      | FStar_Pervasives_Native.Some
          (uu____593,FStar_Pervasives_Native.Some fn) ->
          let uu____609 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____609
      | uu____610 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____635 = FStar_Util.smap_try_find file_system_map key  in
      match uu____635 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____657) ->
          FStar_Pervasives_Native.Some iface
      | uu____672 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____697 = FStar_Util.smap_try_find file_system_map key  in
      match uu____697 with
      | FStar_Pervasives_Native.Some
          (uu____718,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____734 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____755 = interface_of file_system_map key  in
      FStar_Option.isSome uu____755
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____768 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____768
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____776 =
      let uu____777 = FStar_Options.lax ()  in
      if uu____777
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____776
  
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
                      (let uu____814 = lowercase_module_name fn  in
                       key = uu____814)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____823 = interface_of file_system_map key  in
              (match uu____823 with
               | FStar_Pervasives_Native.None  ->
                   let uu____827 =
                     let uu____832 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____832)  in
                   FStar_Errors.raise_err uu____827
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____836 =
                (cmd_line_has_impl key) &&
                  (let uu____838 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____838)
                 in
              if uu____836
              then
                let uu____841 = FStar_Options.expose_interfaces ()  in
                (if uu____841
                 then
                   let uu____842 =
                     let uu____843 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____843  in
                   maybe_add_suffix uu____842
                 else
                   (let uu____847 =
                      let uu____852 =
                        let uu____853 =
                          let uu____854 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____854  in
                        let uu____857 =
                          let uu____858 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____858  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____853 uu____857
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____852)
                       in
                    FStar_Errors.raise_err uu____847))
              else
                (let uu____862 =
                   let uu____863 = interface_of file_system_map key  in
                   FStar_Option.get uu____863  in
                 maybe_add_suffix uu____862)
          | PreferInterface key ->
              let uu____867 = implementation_of file_system_map key  in
              (match uu____867 with
               | FStar_Pervasives_Native.None  ->
                   let uu____871 =
                     let uu____876 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____876)
                      in
                   FStar_Errors.raise_err uu____871
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____879 = implementation_of file_system_map key  in
              (match uu____879 with
               | FStar_Pervasives_Native.None  ->
                   let uu____883 =
                     let uu____888 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____888)
                      in
                   FStar_Errors.raise_err uu____883
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
          let uu____932 = deps_try_find deps fn  in
          match uu____932 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____946) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (add_dependence : dependence_graph -> file_name -> file_name -> unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____987 to_1 =
          match uu____987 with
          | (d,color) ->
              let uu____1007 = is_interface to_1  in
              if uu____1007
              then
                let uu____1014 =
                  let uu____1017 =
                    let uu____1018 = lowercase_module_name to_1  in
                    PreferInterface uu____1018  in
                  uu____1017 :: d  in
                (uu____1014, color)
              else
                (let uu____1022 =
                   let uu____1025 =
                     let uu____1026 = lowercase_module_name to_1  in
                     UseImplementation uu____1026  in
                   uu____1025 :: d  in
                 (uu____1022, color))
           in
        let uu____1029 = deps_try_find deps from  in
        match uu____1029 with
        | FStar_Pervasives_Native.None  ->
            let uu____1040 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____1040
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____1056 = add_dep key_deps to_  in
            deps_add_dep deps from uu____1056
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1069 =
       let uu____1070 =
         let uu____1071 =
           let uu____1072 =
             let uu____1075 =
               let uu____1078 = deps_keys graph  in
               FStar_List.unique uu____1078  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1087 =
                      let uu____1092 = deps_try_find graph k  in
                      FStar_Util.must uu____1092  in
                    FStar_Pervasives_Native.fst uu____1087  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1075
              in
           FStar_String.concat "\n" uu____1072  in
         Prims.strcat uu____1071 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1070  in
     FStar_Util.write_file "dep.graph" uu____1069)
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1127  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1144 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1144  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1170 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1170
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1191 =
              let uu____1196 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1196)  in
            FStar_Errors.raise_err uu____1191)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1242 = FStar_Util.smap_try_find map1 key  in
      match uu____1242 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1279 = is_interface full_path  in
          if uu____1279
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1313 = is_interface full_path  in
          if uu____1313
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1340 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1354  ->
          match uu____1354 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1340);
    FStar_List.iter
      (fun f  ->
         let uu____1365 = lowercase_module_name f  in add_entry uu____1365 f)
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
        (let uu____1386 =
           let uu____1389 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1389  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1415 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1415  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1386);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1553 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1553 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1568 = string_of_lid l last1  in
      FStar_String.lowercase uu____1568
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1574 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1574
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1588 =
        let uu____1589 =
          let uu____1590 =
            let uu____1591 =
              let uu____1594 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1594  in
            FStar_Util.must uu____1591  in
          FStar_String.lowercase uu____1590  in
        uu____1589 <> k'  in
      if uu____1588
      then
        let uu____1595 = FStar_Ident.range_of_lid lid  in
        let uu____1596 =
          let uu____1601 =
            let uu____1602 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1602 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1601)  in
        FStar_Errors.log_issue uu____1595 uu____1596
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1609 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1625 = FStar_Options.prims_basename ()  in
      let uu____1626 =
        let uu____1629 = FStar_Options.pervasives_basename ()  in
        let uu____1630 =
          let uu____1633 = FStar_Options.pervasives_native_basename ()  in
          [uu____1633]  in
        uu____1629 :: uu____1630  in
      uu____1625 :: uu____1626  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1668 =
         let uu____1671 = lowercase_module_name full_filename  in
         namespace_of_module uu____1671  in
       match uu____1668 with
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
          let uu____1961 =
            let uu____1964 = FStar_ST.op_Bang deps1  in d :: uu____1964  in
          FStar_ST.op_Colon_Equals deps1 uu____1961
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2129 = resolve_module_name original_or_working_map key  in
        match uu____2129 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2168 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____2168
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2203 -> false  in
      let record_open_module let_open lid =
        let uu____2217 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2217
        then true
        else
          (if let_open
           then
             (let uu____2220 = FStar_Ident.range_of_lid lid  in
              let uu____2221 =
                let uu____2226 =
                  let uu____2227 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2227  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2226)
                 in
              FStar_Errors.log_issue uu____2220 uu____2221)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2237 = FStar_Ident.range_of_lid lid  in
          let uu____2238 =
            let uu____2243 =
              let uu____2244 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2244
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2243)
             in
          FStar_Errors.log_issue uu____2237 uu____2238
        else ()  in
      let record_open let_open lid =
        let uu____2257 = record_open_module let_open lid  in
        if uu____2257
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2269 =
        match uu____2269 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2276 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2289 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2289  in
        let alias = lowercase_join_longident lid true  in
        let uu____2291 = FStar_Util.smap_try_find original_map alias  in
        match uu____2291 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2345 = FStar_Ident.range_of_lid lid  in
              let uu____2346 =
                let uu____2351 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2351)
                 in
              FStar_Errors.log_issue uu____2345 uu____2346);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2358 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2362 = add_dependence_edge working_map module_name  in
            if uu____2362
            then ()
            else
              (let uu____2364 = FStar_Options.debug_any ()  in
               if uu____2364
               then
                 let uu____2365 = FStar_Ident.range_of_lid lid  in
                 let uu____2366 =
                   let uu____2371 =
                     let uu____2372 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2372
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2371)
                    in
                 FStar_Errors.log_issue uu____2365 uu____2366
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___107_2488 =
         match uu___107_2488 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2497 =
                   let uu____2498 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2498  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2502) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2509 =
                   let uu____2510 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2510  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___108_2519 =
         match uu___108_2519 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2524 = record_module_alias ident lid  in
             if uu____2524
             then
               let uu____2525 =
                 let uu____2526 = lowercase_join_longident lid true  in
                 PreferInterface uu____2526  in
               add_dep deps uu____2525
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2561,patterms) ->
             FStar_List.iter
               (fun uu____2583  ->
                  match uu____2583 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____2592,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____2598,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2600;
               FStar_Parser_AST.mdest = uu____2601;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2603;
               FStar_Parser_AST.mdest = uu____2604;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2606,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2608;
               FStar_Parser_AST.mdest = uu____2609;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2613,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2643  -> match uu____2643 with | (x,docnik) -> x)
                 ts
                in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2656,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2663 -> ()
         | FStar_Parser_AST.Pragma uu____2664 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2700 =
                 let uu____2701 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2701 > (Prims.parse_int "1")  in
               if uu____2700
               then
                 let uu____2743 =
                   let uu____2748 =
                     let uu____2749 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2749
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2748)  in
                 let uu____2750 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____2743 uu____2750
               else ()))
       
       and collect_tycon uu___109_2752 =
         match uu___109_2752 with
         | FStar_Parser_AST.TyconAbstract (uu____2753,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2765,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2779,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2825  ->
                   match uu____2825 with
                   | (uu____2834,t,uu____2836) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2841,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2900  ->
                   match uu____2900 with
                   | (uu____2913,t,uu____2915,uu____2916) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___110_2925 =
         match uu___110_2925 with
         | FStar_Parser_AST.DefineEffect (uu____2926,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2940,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___111_2951 =
         match uu___111_2951 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2952,t);
             FStar_Parser_AST.brange = uu____2954;
             FStar_Parser_AST.blevel = uu____2955;
             FStar_Parser_AST.aqual = uu____2956;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2957,t);
             FStar_Parser_AST.brange = uu____2959;
             FStar_Parser_AST.blevel = uu____2960;
             FStar_Parser_AST.aqual = uu____2961;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2963;
             FStar_Parser_AST.blevel = uu____2964;
             FStar_Parser_AST.aqual = uu____2965;_} -> collect_term t
         | uu____2966 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___112_2968 =
         match uu___112_2968 with
         | FStar_Const.Const_int
             (uu____2969,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____2984 =
               let uu____2985 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____2985  in
             add_dep deps uu____2984
         | FStar_Const.Const_char uu____3019 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3054 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3088 -> ()
       
       and collect_term' uu___113_3089 =
         match uu___113_3089 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____3098 =
                 let uu____3099 = FStar_Ident.text_of_id s  in
                 uu____3099 = "@"  in
               if uu____3098
               then
                 let uu____3100 =
                   let uu____3101 =
                     let uu____3102 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____3102
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3101  in
                 collect_term' uu____3100
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3104 -> ()
         | FStar_Parser_AST.Uvar uu____3105 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3108) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3138  ->
                   match uu____3138 with | (t,uu____3144) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3154) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3156,patterms,t) ->
             (FStar_List.iter
                (fun uu____3206  ->
                   match uu____3206 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3235 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3244,t1,t2) ->
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
                (fun uu____3340  ->
                   match uu____3340 with | (uu____3345,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3348) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3404,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3408) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3414) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3420,uu____3421) ->
             collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Quote uu____3423 -> ()
         | FStar_Parser_AST.Antiquote uu____3428 -> ()
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___114_3440 =
         match uu___114_3440 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3441 -> ()
         | FStar_Parser_AST.PatConst uu____3442 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3450 -> ()
         | FStar_Parser_AST.PatName uu____3457 -> ()
         | FStar_Parser_AST.PatTvar uu____3458 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3472) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3491  ->
                  match uu____3491 with | (uu____3496,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3541 =
         match uu____3541 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3559 = FStar_Parser_Driver.parse_file filename  in
       match uu____3559 with
       | (ast,uu____3579) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3594 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____3594
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3630 = FStar_ST.op_Bang deps  in
             let uu____3678 = FStar_ST.op_Bang mo_roots  in
             (uu____3630, uu____3678))))
  
let (collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap FStar_ST.ref)
  =
  let uu____3753 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____3753 
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
              let uu____3878 = FStar_Options.find_file fn  in
              match uu____3878 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3881 =
                    let uu____3886 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3886)  in
                  FStar_Errors.raise_err uu____3881
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3896 =
        let uu____3897 = deps_try_find dep_graph file_name  in
        uu____3897 = FStar_Pervasives_Native.None  in
      if uu____3896
      then
        let uu____3914 =
          let uu____3923 =
            let uu____3934 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____3934 file_name  in
          match uu____3923 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____3914 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____4039 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____4039
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____4044 =
                let uu____4049 = FStar_List.unique deps1  in
                (uu____4049, White)  in
              deps_add_dep dep_graph file_name uu____4044);
             (let uu____4050 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____4050))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let dep_graph_copy =
       let uu____4056 = dep_graph  in
       match uu____4056 with
       | Deps g ->
           let uu____4064 = FStar_Util.smap_copy g  in Deps uu____4064
        in
     let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____4098 =
          let uu____4103 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____4103)  in
        FStar_Errors.raise_err uu____4098)
        in
     let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec aux cycle filename =
         let uu____4138 =
           let uu____4143 = deps_try_find dep_graph filename  in
           FStar_Util.must uu____4143  in
         match uu____4138 with
         | (direct_deps,color) ->
             (match color with
              | Gray  -> cycle_detected dep_graph cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____4158 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4158);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____4164 =
                      let uu____4167 = FStar_ST.op_Bang topologically_sorted
                         in
                      filename :: uu____4167  in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____4164)))
          in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted  in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy  in
       let rec aux cycle filename =
         let uu____4332 =
           let uu____4339 = deps_try_find dep_graph1 filename  in
           match uu____4339 with
           | FStar_Pervasives_Native.Some (d,c) -> (d, c)
           | FStar_Pervasives_Native.None  ->
               let uu____4364 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____4364
            in
         match uu____4332 with
         | (direct_deps,color) ->
             let direct_deps1 =
               FStar_All.pipe_right direct_deps
                 (FStar_List.collect
                    (fun x  ->
                       match x with
                       | UseInterface f ->
                           let uu____4387 =
                             implementation_of file_system_map f  in
                           (match uu____4387 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4393 -> [x; UseImplementation f])
                       | PreferInterface f ->
                           let uu____4397 =
                             implementation_of file_system_map f  in
                           (match uu____4397 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4403 -> [x; UseImplementation f])
                       | uu____4406 -> [x]))
                in
             (match color with
              | Gray  -> cycle_detected dep_graph1 cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph1 filename (direct_deps1, Gray);
                   (let uu____4409 =
                      dependences_of file_system_map dep_graph1
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4409);
                   deps_add_dep dep_graph1 filename (direct_deps1, Black)))
          in
       FStar_List.iter (aux []) all_command_line_files  in
     full_cycle_detection all_cmd_line_files1;
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let uu____4422 = topological_dependences_of all_cmd_line_files1  in
      (uu____4422, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____4439  ->
    fun f  ->
      match uu____4439 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____4468  ->
    fun fn  ->
      match uu____4468 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____4486 = FStar_Options.find_file fn  in
            match uu____4486 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____4490 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____4501 = FStar_Options.debug_any ()  in
             if uu____4501
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____4512 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____4512
            then
              let uu____4519 =
                let uu____4524 =
                  let uu____4525 =
                    let uu____4526 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____4526  in
                  digest_of_file1 uu____4525  in
                ("interface", uu____4524)  in
              [uu____4519]
            else []  in
          let binary_deps =
            let uu____4545 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____4545
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____4555 =
                      (is_interface fn2) &&
                        (let uu____4557 = lowercase_module_name fn2  in
                         uu____4557 = module_name)
                       in
                    Prims.op_Negation uu____4555))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____4567 = lowercase_module_name fn11  in
                   let uu____4568 = lowercase_module_name fn2  in
                   FStar_String.compare uu____4567 uu____4568) binary_deps
             in
          let rec hash_deps out uu___115_4595 =
            match uu___115_4595 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4639 =
                    let uu____4646 =
                      let uu____4651 = lowercase_module_name fn2  in
                      let uu____4652 = digest_of_file1 cache_fn  in
                      (uu____4651, uu____4652)  in
                    uu____4646 :: out  in
                  hash_deps uu____4639 deps1
                else
                  ((let uu____4659 = FStar_Options.debug_any ()  in
                    if uu____4659
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
    let uu____4688 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4707  ->
              match uu____4707 with
              | (m,d) ->
                  let uu____4714 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4714))
       in
    FStar_All.pipe_right uu____4688 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____4721  ->
    match uu____4721 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4741 =
                  let uu____4746 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4746 FStar_Option.get  in
                match uu____4741 with
                | (f_deps,uu____4768) ->
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
  fun uu____4782  ->
    match uu____4782 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____4823 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____4823) ||
              (let uu____4827 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____4827)
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
                let uu____4854 =
                  let uu____4857 = FStar_ST.op_Bang order  in ml_file ::
                    uu____4857
                   in
                FStar_ST.op_Colon_Equals order uu____4854
             in
          let rec aux uu___116_4957 =
            match uu___116_4957 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____4975 = deps_try_find deps file_name  in
                      (match uu____4975 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____4986 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____4986
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____4988) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____4999 = should_visit lc_module_name  in
                  if uu____4999
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____5004 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____5004);
                     (let uu____5008 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____5008);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____5016 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____5016)
           in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____5079 =
              let uu____5080 =
                let uu____5083 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____5083  in
              FStar_Option.get uu____5080  in
            FStar_Util.replace_chars uu____5079 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____5098 = output_file ".ml" f  in norm_path uu____5098  in
        let output_krml_file f =
          let uu____5105 = output_file ".krml" f  in norm_path uu____5105  in
        let output_cmx_file f =
          let uu____5112 = output_file ".cmx" f  in norm_path uu____5112  in
        let cache_file f =
          let uu____5119 = cache_file_name f  in norm_path uu____5119  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____5162 =
                   let uu____5169 = deps_try_find deps f  in
                   FStar_All.pipe_right uu____5169 FStar_Option.get  in
                 match uu____5162 with
                 | (f_deps,uu____5193) ->
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
                     ((let uu____5213 = is_interface f  in
                       if uu____5213
                       then
                         let uu____5214 =
                           let uu____5215 =
                             FStar_Options.prepend_cache_dir norm_f  in
                           norm_path uu____5215  in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____5214 norm_f files3
                       else ());
                      (let uu____5218 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5218
                         norm_f files3);
                      (let already_there =
                         let uu____5222 =
                           let uu____5233 =
                             let uu____5234 = output_file ".krml" f  in
                             norm_path uu____5234  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____5233
                            in
                         match uu____5222 with
                         | FStar_Pervasives_Native.Some
                             (uu____5245,already_there,uu____5247) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____5269 =
                          let uu____5270 = output_file ".krml" f  in
                          norm_path uu____5270  in
                        let uu____5271 =
                          let uu____5280 =
                            let uu____5281 = output_file ".exe" f  in
                            norm_path uu____5281  in
                          let uu____5282 =
                            let uu____5285 =
                              let uu____5288 =
                                let uu____5291 =
                                  deps_of
                                    (Mk
                                       (deps, file_system_map,
                                         all_cmd_line_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____5299 = output_file ".krml" x
                                        in
                                     norm_path uu____5299) uu____5291
                                 in
                              FStar_List.append already_there uu____5288  in
                            FStar_List.unique uu____5285  in
                          (uu____5280, uu____5282, false)  in
                        FStar_Util.smap_add transitive_krml uu____5269
                          uu____5271);
                       (let uu____5310 = is_implementation f  in
                        if uu____5310
                        then
                          ((let uu____5312 = output_ml_file f  in
                            let uu____5313 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5312
                              uu____5313);
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
                                        (let uu____5337 =
                                           lowercase_module_name df  in
                                         let uu____5338 =
                                           lowercase_module_name f  in
                                         uu____5337 <> uu____5338) &&
                                          (let uu____5340 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____5340)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____5346 =
                               let uu____5347 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____5347  in
                             if uu____5346
                             then
                               let uu____5348 = output_cmx_file f  in
                               let uu____5349 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____5348 uu____5349
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____5351 = output_krml_file f  in
                             let uu____5352 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5351
                               uu____5352)))
                        else
                          (let uu____5354 =
                             (let uu____5357 =
                                let uu____5358 = lowercase_module_name f  in
                                has_implementation file_system_map uu____5358
                                 in
                              Prims.op_Negation uu____5357) &&
                               (is_interface f)
                              in
                           if uu____5354
                           then
                             let uu____5359 = output_krml_file f  in
                             let uu____5360 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5359
                               uu____5360
                           else ()))))));
         (let all_fst_files =
            let uu____5365 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____5365
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5391 = FStar_Options.should_extract mname  in
                    if uu____5391
                    then
                      let uu____5392 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____5392
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5408 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____5408));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____5421 =
              let uu____5430 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____5430  in
            match uu____5421 with
            | (exe,deps1,seen) ->
                if seen
                then (exe, deps1)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                   (let deps2 =
                      let uu____5493 =
                        let uu____5496 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____5508 = make_transitive dep1  in
                               match uu____5508 with
                               | (uu____5517,deps2) -> dep1 :: deps2) deps1
                           in
                        FStar_List.flatten uu____5496  in
                      FStar_List.unique uu____5493  in
                    FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                    (exe, deps2)))
             in
          (let uu____5537 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____5556 = make_transitive f  in
                match uu____5556 with
                | (exe,deps1) ->
                    let deps2 =
                      let uu____5570 = FStar_List.unique (f :: deps1)  in
                      FStar_String.concat " " uu____5570  in
                    let wasm =
                      let uu____5574 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____5574 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____5537);
          (let uu____5577 =
             let uu____5578 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5578 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5577);
          (let uu____5588 =
             let uu____5589 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5589 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5588);
          (let uu____5598 =
             let uu____5599 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5599 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5598)))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____5613 = FStar_Options.dep ()  in
    match uu____5613 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____5616 = deps  in
        (match uu____5616 with
         | Mk (deps1,uu____5618,uu____5619) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____5624 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  