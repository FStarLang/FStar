open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut [@@deriving show]
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____4 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____8 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____12 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White 
  | Gray 
  | Black [@@deriving show]
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____26 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____30 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____34 -> false 
type open_kind =
  | Open_module 
  | Open_namespace [@@deriving show]
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____38 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____42 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____68 =
             (l > lext) &&
               (let uu____80 = FStar_String.substring f (l - lext) lext  in
                uu____80 = ext)
              in
           if uu____68
           then
             let uu____97 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____97
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____109 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____109 with
    | (FStar_Pervasives_Native.Some m)::uu____119 ->
        FStar_Pervasives_Native.Some m
    | uu____126 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____134 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____134 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____141 = is_interface f  in Prims.op_Negation uu____141 
let list_of_option :
  'Auu____144 .
    'Auu____144 FStar_Pervasives_Native.option -> 'Auu____144 Prims.list
  =
  fun uu___55_152  ->
    match uu___55_152 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____158 .
    ('Auu____158 FStar_Pervasives_Native.option,'Auu____158
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____158 Prims.list
  =
  fun uu____172  ->
    match uu____172 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____194 =
      let uu____197 = FStar_Util.basename f  in
      check_and_strip_suffix uu____197  in
    match uu____194 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____199 =
          let uu____204 = FStar_Util.format1 "not a valid FStar file: %s\n" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____204)  in
        FStar_Errors.raise_err uu____199
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____208 = module_name_of_file f  in
    FStar_String.lowercase uu____208
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____215 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____215 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____218 ->
        let uu____221 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____221
  
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name [@@deriving show]
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____238 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____250 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____262 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences : 'Auu____273 . Prims.unit -> 'Auu____273 Prims.list =
  fun uu____276  -> [] 
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
  fun uu____365  ->
    fun k  -> match uu____365 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____394  ->
    fun k  ->
      fun v1  -> match uu____394 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____416  -> match uu____416 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : Prims.unit -> dependence_graph) =
  fun uu____432  ->
    let uu____433 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____433
  
let (empty_deps : deps) =
  let uu____444 =
    let uu____453 = deps_empty ()  in
    let uu____454 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____453, uu____454, [])  in
  Mk uu____444 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___56_487  ->
    match uu___56_487 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____501 = FStar_Util.smap_try_find file_system_map key  in
      match uu____501 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____523) ->
          let uu____538 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____538
      | FStar_Pervasives_Native.Some
          (uu____539,FStar_Pervasives_Native.Some fn) ->
          let uu____555 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____555
      | uu____556 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____577 = FStar_Util.smap_try_find file_system_map key  in
      match uu____577 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____599) ->
          FStar_Pervasives_Native.Some iface
      | uu____614 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____635 = FStar_Util.smap_try_find file_system_map key  in
      match uu____635 with
      | FStar_Pervasives_Native.Some
          (uu____656,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____672 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____689 = interface_of file_system_map key  in
      FStar_Option.isSome uu____689
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____698 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____698
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____704 =
      let uu____705 = FStar_Options.lax ()  in
      if uu____705
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____704
  
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
                      (let uu____732 = lowercase_module_name fn  in
                       key = uu____732)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____739 = interface_of file_system_map key  in
              (match uu____739 with
               | FStar_Pervasives_Native.None  ->
                   let uu____745 =
                     let uu____750 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____750)  in
                   FStar_Errors.raise_err uu____745
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____754 =
                (cmd_line_has_impl key) &&
                  (let uu____756 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____756)
                 in
              if uu____754
              then
                let uu____759 = FStar_Options.expose_interfaces ()  in
                (if uu____759
                 then
                   let uu____760 =
                     let uu____761 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____761  in
                   maybe_add_suffix uu____760
                 else
                   (let uu____765 =
                      let uu____770 =
                        let uu____771 =
                          let uu____772 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____772  in
                        let uu____775 =
                          let uu____776 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____776  in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____771 uu____775
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____770)
                       in
                    FStar_Errors.raise_err uu____765))
              else
                (let uu____780 =
                   let uu____781 = interface_of file_system_map key  in
                   FStar_Option.get uu____781  in
                 maybe_add_suffix uu____780)
          | PreferInterface key ->
              let uu____785 = implementation_of file_system_map key  in
              (match uu____785 with
               | FStar_Pervasives_Native.None  ->
                   let uu____791 =
                     let uu____796 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____796)
                      in
                   FStar_Errors.raise_err uu____791
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____799 = implementation_of file_system_map key  in
              (match uu____799 with
               | FStar_Pervasives_Native.None  ->
                   let uu____805 =
                     let uu____810 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____810)
                      in
                   FStar_Errors.raise_err uu____805
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
          let uu____840 = deps_try_find deps fn  in
          match uu____840 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____854) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (add_dependence :
  dependence_graph -> file_name -> file_name -> Prims.unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____885 to_1 =
          match uu____885 with
          | (d,color) ->
              let uu____905 = is_interface to_1  in
              if uu____905
              then
                let uu____912 =
                  let uu____915 =
                    let uu____916 = lowercase_module_name to_1  in
                    PreferInterface uu____916  in
                  uu____915 :: d  in
                (uu____912, color)
              else
                (let uu____920 =
                   let uu____923 =
                     let uu____924 = lowercase_module_name to_1  in
                     UseImplementation uu____924  in
                   uu____923 :: d  in
                 (uu____920, color))
           in
        let uu____927 = deps_try_find deps from  in
        match uu____927 with
        | FStar_Pervasives_Native.None  ->
            let uu____938 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____938
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____954 = add_dep key_deps to_  in
            deps_add_dep deps from uu____954
  
let (print_graph : dependence_graph -> Prims.unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____965 =
       let uu____966 =
         let uu____967 =
           let uu____968 =
             let uu____971 =
               let uu____974 = deps_keys graph  in
               FStar_List.unique uu____974  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____983 =
                      let uu____988 = deps_try_find graph k  in
                      FStar_Util.must uu____988  in
                    FStar_Pervasives_Native.fst uu____983  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____971
              in
           FStar_String.concat "\n" uu____968  in
         Prims.strcat uu____967 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____966  in
     FStar_Util.write_file "dep.graph" uu____965)
  
let (build_inclusion_candidates_list :
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1017  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1034 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1034  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1060 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1060
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1081 =
              let uu____1086 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1086)  in
            FStar_Errors.raise_err uu____1081)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1126 = FStar_Util.smap_try_find map1 key  in
      match uu____1126 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1163 = is_interface full_path  in
          if uu____1163
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1197 = is_interface full_path  in
          if uu____1197
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1224 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1238  ->
          match uu____1238 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1224);
    FStar_List.iter
      (fun f  ->
         let uu____1249 = lowercase_module_name f  in add_entry uu____1249 f)
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
        (let uu____1264 =
           let uu____1267 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1267  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1293 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1293  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1264);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1427 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1427 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1438 = string_of_lid l last1  in
      FStar_String.lowercase uu____1438
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1442 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1442
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> Prims.unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1452 =
        let uu____1453 =
          let uu____1454 =
            let uu____1455 =
              let uu____1458 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1458  in
            FStar_Util.must uu____1455  in
          FStar_String.lowercase uu____1454  in
        uu____1453 <> k'  in
      if uu____1452
      then
        let uu____1459 = FStar_Ident.range_of_lid lid  in
        let uu____1460 =
          let uu____1465 =
            let uu____1466 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1466 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1465)  in
        FStar_Errors.log_issue uu____1459 uu____1460
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1471 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1485 = FStar_Options.prims_basename ()  in
      let uu____1486 =
        let uu____1489 = FStar_Options.pervasives_basename ()  in
        let uu____1490 =
          let uu____1493 = FStar_Options.pervasives_native_basename ()  in
          [uu____1493]  in
        uu____1489 :: uu____1490  in
      uu____1485 :: uu____1486  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1528 =
         let uu____1531 = lowercase_module_name full_filename  in
         namespace_of_module uu____1531  in
       match uu____1528 with
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
        let uu____1720 =
          let uu____1721 =
            let uu____1722 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (fun d'  -> d' = d) uu____1722  in
          Prims.op_Negation uu____1721  in
        if uu____1720
        then
          let uu____1792 =
            let uu____1795 = FStar_ST.op_Bang deps1  in d :: uu____1795  in
          FStar_ST.op_Colon_Equals deps1 uu____1792
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____1956 = resolve_module_name original_or_working_map key  in
        match uu____1956 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____1995 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____1997 = FStar_Options.dep ()  in
                   uu____1997 = (FStar_Pervasives_Native.Some "full"))
                 in
              if uu____1995
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2036 -> false  in
      let record_open_module let_open lid =
        let uu____2046 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2046
        then true
        else
          (if let_open
           then
             (let uu____2049 = FStar_Ident.range_of_lid lid  in
              let uu____2050 =
                let uu____2055 =
                  let uu____2056 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2056  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2055)
                 in
              FStar_Errors.log_issue uu____2049 uu____2050)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2064 = FStar_Ident.range_of_lid lid  in
          let uu____2065 =
            let uu____2070 =
              let uu____2071 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2071
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2070)
             in
          FStar_Errors.log_issue uu____2064 uu____2065
        else ()  in
      let record_open let_open lid =
        let uu____2080 = record_open_module let_open lid  in
        if uu____2080
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2090 =
        match uu____2090 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2097 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2106 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2106  in
        let alias = lowercase_join_longident lid true  in
        let uu____2108 = FStar_Util.smap_try_find original_map alias  in
        match uu____2108 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2162 = FStar_Ident.range_of_lid lid  in
              let uu____2163 =
                let uu____2168 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2168)
                 in
              FStar_Errors.log_issue uu____2162 uu____2163);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2173 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2177 = add_dependence_edge working_map module_name  in
            if uu____2177
            then ()
            else
              (let uu____2179 = FStar_Options.debug_any ()  in
               if uu____2179
               then
                 let uu____2180 = FStar_Ident.range_of_lid lid  in
                 let uu____2181 =
                   let uu____2186 =
                     let uu____2187 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2187
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2186)
                    in
                 FStar_Errors.log_issue uu____2180 uu____2181
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___57_2273 =
         match uu___57_2273 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2282 =
                   let uu____2283 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2283  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2287) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2294 =
                   let uu____2295 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2295  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___58_2304 =
         match uu___58_2304 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2309 = record_module_alias ident lid  in
             if uu____2309
             then
               let uu____2310 =
                 let uu____2311 = lowercase_join_longident lid true  in
                 PreferInterface uu____2311  in
               add_dep deps uu____2310
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2346,patterms) ->
             FStar_List.iter
               (fun uu____2368  ->
                  match uu____2368 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____2377,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____2383,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2385;
               FStar_Parser_AST.mdest = uu____2386;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2388;
               FStar_Parser_AST.mdest = uu____2389;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2391,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2393;
               FStar_Parser_AST.mdest = uu____2394;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2398,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2428  -> match uu____2428 with | (x,docnik) -> x)
                 ts
                in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2441,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2448 -> ()
         | FStar_Parser_AST.Pragma uu____2449 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2485 =
                 let uu____2486 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2486 > (Prims.parse_int "1")  in
               if uu____2485
               then
                 let uu____2528 =
                   let uu____2533 =
                     let uu____2534 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2534
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2533)  in
                 let uu____2535 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____2528 uu____2535
               else ()))
       
       and collect_tycon uu___59_2537 =
         match uu___59_2537 with
         | FStar_Parser_AST.TyconAbstract (uu____2538,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2550,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2564,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2610  ->
                   match uu____2610 with
                   | (uu____2619,t,uu____2621) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2626,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2685  ->
                   match uu____2685 with
                   | (uu____2698,t,uu____2700,uu____2701) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___60_2710 =
         match uu___60_2710 with
         | FStar_Parser_AST.DefineEffect (uu____2711,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2725,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___61_2736 =
         match uu___61_2736 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2737,t);
             FStar_Parser_AST.brange = uu____2739;
             FStar_Parser_AST.blevel = uu____2740;
             FStar_Parser_AST.aqual = uu____2741;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2742,t);
             FStar_Parser_AST.brange = uu____2744;
             FStar_Parser_AST.blevel = uu____2745;
             FStar_Parser_AST.aqual = uu____2746;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2748;
             FStar_Parser_AST.blevel = uu____2749;
             FStar_Parser_AST.aqual = uu____2750;_} -> collect_term t
         | uu____2751 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___62_2753 =
         match uu___62_2753 with
         | FStar_Const.Const_int
             (uu____2754,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____2769 =
               let uu____2770 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____2770  in
             add_dep deps uu____2769
         | FStar_Const.Const_char uu____2804 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____2838 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____2872 -> ()
       
       and collect_term' uu___63_2873 =
         match uu___63_2873 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____2882 =
                 let uu____2883 = FStar_Ident.text_of_id s  in
                 uu____2883 = "@"  in
               if uu____2882
               then
                 let uu____2884 =
                   let uu____2885 =
                     let uu____2886 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____2886
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____2885  in
                 collect_term' uu____2884
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____2888 -> ()
         | FStar_Parser_AST.Uvar uu____2889 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____2892) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____2922  ->
                   match uu____2922 with | (t,uu____2928) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____2938) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____2940,patterms,t) ->
             (FStar_List.iter
                (fun uu____2990  ->
                   match uu____2990 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3019 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3030,t1,t2) ->
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
                (fun uu____3126  ->
                   match uu____3126 with | (uu____3131,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3134) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3190,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3194) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3200) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3206,uu____3207) ->
             collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Quote uu____3209 -> ()
         | FStar_Parser_AST.Antiquote uu____3214 -> ()
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___64_3226 =
         match uu___64_3226 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3227 -> ()
         | FStar_Parser_AST.PatConst uu____3228 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3236 -> ()
         | FStar_Parser_AST.PatName uu____3243 -> ()
         | FStar_Parser_AST.PatTvar uu____3244 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3258) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3277  ->
                  match uu____3277 with | (uu____3282,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3327 =
         match uu____3327 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3345 = FStar_Parser_Driver.parse_file filename  in
       match uu____3345 with
       | (ast,uu____3365) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3380 =
               ((is_interface filename) &&
                  (has_implementation original_map mname))
                 &&
                 (let uu____3382 = FStar_Options.dep ()  in
                  uu____3382 = (FStar_Pervasives_Native.Some "full"))
                in
             if uu____3380
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3422 = FStar_ST.op_Bang deps  in
             let uu____3470 = FStar_ST.op_Bang mo_roots  in
             (uu____3422, uu____3470))))
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____3552 = FStar_Options.find_file fn  in
              match uu____3552 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3555 =
                    let uu____3560 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3560)  in
                  FStar_Errors.raise_err uu____3555
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3568 =
        let uu____3569 = deps_try_find dep_graph file_name  in
        uu____3569 = FStar_Pervasives_Native.None  in
      if uu____3568
      then
        let uu____3586 = collect_one file_system_map file_name  in
        match uu____3586 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____3609 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____3609
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____3614 =
                let uu____3619 = FStar_List.unique deps1  in
                (uu____3619, White)  in
              deps_add_dep dep_graph file_name uu____3614);
             (let uu____3624 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____3624))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec aux cycle filename =
         let uu____3657 =
           let uu____3662 = deps_try_find dep_graph filename  in
           FStar_Util.must uu____3662  in
         match uu____3657 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  ((let uu____3676 =
                      let uu____3681 =
                        FStar_Util.format1
                          "Recursive dependency on module %s\n" filename
                         in
                      (FStar_Errors.Warning_RecursiveDependency, uu____3681)
                       in
                    FStar_Errors.log_issue FStar_Range.dummyRange uu____3676);
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____3687 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3687);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3693 =
                      let uu____3696 = FStar_ST.op_Bang topologically_sorted
                         in
                      filename :: uu____3696  in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3693)))
          in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted  in
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let uu____3842 = topological_dependences_of all_cmd_line_files1  in
      (uu____3842, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____3855  ->
    fun f  ->
      match uu____3855 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____3880  ->
    fun fn  ->
      match uu____3880 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____3898 = FStar_Options.find_file fn  in
            match uu____3898 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____3902 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____3911 = FStar_Options.debug_any ()  in
             if uu____3911
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____3922 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____3922
            then
              let uu____3929 =
                let uu____3934 =
                  let uu____3935 =
                    let uu____3936 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____3936  in
                  digest_of_file1 uu____3935  in
                ("interface", uu____3934)  in
              [uu____3929]
            else []  in
          let binary_deps =
            let uu____3955 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____3955
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____3965 =
                      (is_interface fn2) &&
                        (let uu____3967 = lowercase_module_name fn2  in
                         uu____3967 = module_name)
                       in
                    Prims.op_Negation uu____3965))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____3977 = lowercase_module_name fn11  in
                   let uu____3978 = lowercase_module_name fn2  in
                   FStar_String.compare uu____3977 uu____3978) binary_deps
             in
          let rec hash_deps out uu___65_4001 =
            match uu___65_4001 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4045 =
                    let uu____4052 =
                      let uu____4057 = lowercase_module_name fn2  in
                      let uu____4058 = digest_of_file1 cache_fn  in
                      (uu____4057, uu____4058)  in
                    uu____4052 :: out  in
                  hash_deps uu____4045 deps1
                else
                  ((let uu____4065 = FStar_Options.debug_any ()  in
                    if uu____4065
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
    let uu____4092 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4111  ->
              match uu____4111 with
              | (m,d) ->
                  let uu____4118 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4118))
       in
    FStar_All.pipe_right uu____4092 (FStar_String.concat "\n")
  
let (print_make : deps -> Prims.unit) =
  fun uu____4123  ->
    match uu____4123 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4143 =
                  let uu____4148 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4148 FStar_Option.get  in
                match uu____4143 with
                | (f_deps,uu____4170) ->
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
  
let (print_full : deps -> Prims.unit) =
  fun uu____4182  ->
    match uu____4182 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____4219 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____4219) ||
              (let uu____4223 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____4223)
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
                let uu____4246 =
                  let uu____4249 = FStar_ST.op_Bang order  in ml_file ::
                    uu____4249
                   in
                FStar_ST.op_Colon_Equals order uu____4246
             in
          let rec aux uu___66_4347 =
            match uu___66_4347 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____4363 = deps_try_find deps file_name  in
                      (match uu____4363 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____4374 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____4374
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____4376) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____4387 = should_visit lc_module_name  in
                  if uu____4387
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____4392 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____4392);
                     (let uu____4396 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____4396);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____4404 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____4404)
           in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____4463 =
              let uu____4464 =
                let uu____4467 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____4467  in
              FStar_Option.get uu____4464  in
            FStar_Util.replace_chars uu____4463 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____4478 = output_file ".ml" f  in norm_path uu____4478  in
        let output_krml_file f =
          let uu____4483 = output_file ".krml" f  in norm_path uu____4483  in
        let output_cmx_file f =
          let uu____4488 = output_file ".cmx" f  in norm_path uu____4488  in
        let cache_file f =
          let uu____4493 = cache_file_name f  in norm_path uu____4493  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4536 =
                   let uu____4541 = deps_try_find deps f  in
                   FStar_All.pipe_right uu____4541 FStar_Option.get  in
                 match uu____4536 with
                 | (f_deps,uu____4563) ->
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
                     ((let uu____4579 = is_interface f  in
                       if uu____4579
                       then
                         let uu____4580 =
                           let uu____4581 =
                             FStar_Options.prepend_cache_dir norm_f  in
                           norm_path uu____4581  in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____4580 norm_f files3
                       else ());
                      (let uu____4584 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4584
                         norm_f files3);
                      (let already_there =
                         let uu____4588 =
                           let uu____4599 =
                             let uu____4600 = output_file ".krml" f  in
                             norm_path uu____4600  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____4599
                            in
                         match uu____4588 with
                         | FStar_Pervasives_Native.Some
                             (uu____4611,already_there,uu____4613) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____4635 =
                          let uu____4636 = output_file ".krml" f  in
                          norm_path uu____4636  in
                        let uu____4637 =
                          let uu____4646 =
                            let uu____4647 = output_file ".exe" f  in
                            norm_path uu____4647  in
                          let uu____4648 =
                            let uu____4651 =
                              let uu____4654 =
                                let uu____4657 =
                                  deps_of
                                    (Mk
                                       (deps, file_system_map,
                                         all_cmd_line_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____4665 = output_file ".krml" x
                                        in
                                     norm_path uu____4665) uu____4657
                                 in
                              FStar_List.append already_there uu____4654  in
                            FStar_List.unique uu____4651  in
                          (uu____4646, uu____4648, false)  in
                        FStar_Util.smap_add transitive_krml uu____4635
                          uu____4637);
                       (let uu____4676 = is_implementation f  in
                        if uu____4676
                        then
                          ((let uu____4678 = output_ml_file f  in
                            let uu____4679 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____4678
                              uu____4679);
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
                                        (let uu____4701 =
                                           lowercase_module_name df  in
                                         let uu____4702 =
                                           lowercase_module_name f  in
                                         uu____4701 <> uu____4702) &&
                                          (let uu____4704 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____4704)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____4710 =
                               let uu____4711 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____4711  in
                             if uu____4710
                             then
                               let uu____4712 = output_cmx_file f  in
                               let uu____4713 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____4712 uu____4713
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____4715 = output_krml_file f  in
                             let uu____4716 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____4715
                               uu____4716)))
                        else
                          (let uu____4718 =
                             (let uu____4721 =
                                let uu____4722 = lowercase_module_name f  in
                                has_implementation file_system_map uu____4722
                                 in
                              Prims.op_Negation uu____4721) &&
                               (is_interface f)
                              in
                           if uu____4718
                           then
                             let uu____4723 = output_krml_file f  in
                             let uu____4724 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____4723
                               uu____4724
                           else ()))))));
         (let all_fst_files =
            let uu____4729 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____4729
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____4755 = FStar_Options.should_extract mname  in
                    if uu____4755
                    then
                      let uu____4756 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____4756
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____4772 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____4772));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____4783 =
              let uu____4792 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____4792  in
            match uu____4783 with
            | (exe,deps1,seen) ->
                if seen
                then (exe, deps1)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                   (let deps2 =
                      let uu____4855 =
                        let uu____4858 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____4870 = make_transitive dep1  in
                               match uu____4870 with
                               | (uu____4879,deps2) -> dep1 :: deps2) deps1
                           in
                        FStar_List.flatten uu____4858  in
                      FStar_List.unique uu____4855  in
                    FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                    (exe, deps2)))
             in
          (let uu____4899 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____4918 = make_transitive f  in
                match uu____4918 with
                | (exe,deps1) ->
                    let deps2 =
                      let uu____4932 = FStar_List.unique (f :: deps1)  in
                      FStar_String.concat " " uu____4932  in
                    let wasm =
                      let uu____4936 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____4936 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____4899);
          (let uu____4939 =
             let uu____4940 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____4940 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____4939);
          (let uu____4950 =
             let uu____4951 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____4951 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____4950);
          (let uu____4960 =
             let uu____4961 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____4961 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____4960)))
  
let (print : deps -> Prims.unit) =
  fun deps  ->
    let uu____4973 = FStar_Options.dep ()  in
    match uu____4973 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4976 = deps  in
        (match uu____4976 with
         | Mk (deps1,uu____4978,uu____4979) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4984 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  