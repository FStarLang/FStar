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
let (interface_filename : Prims.string -> Prims.string) =
  fun f  ->
    let uu____145 = is_interface f  in
    if uu____145
    then f
    else
      (let uu____147 =
         let uu____148 = check_and_strip_suffix f  in
         FStar_All.pipe_right uu____148 FStar_Util.must  in
       FStar_All.pipe_right uu____147 (fun x  -> Prims.strcat x ".fsti"))
  
let list_of_option :
  'Auu____157 .
    'Auu____157 FStar_Pervasives_Native.option -> 'Auu____157 Prims.list
  =
  fun uu___53_165  ->
    match uu___53_165 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____171 .
    ('Auu____171 FStar_Pervasives_Native.option,'Auu____171
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____171 Prims.list
  =
  fun uu____185  ->
    match uu____185 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____207 =
      let uu____210 = FStar_Util.basename f  in
      check_and_strip_suffix uu____210  in
    match uu____207 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____212 =
          let uu____217 = FStar_Util.format1 "not a valid FStar file: %s\n" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____217)  in
        FStar_Errors.raise_err uu____212
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____221 = module_name_of_file f  in
    FStar_String.lowercase uu____221
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      FStar_Ident.lid_of_path (FStar_Ident.path_of_text f)
        FStar_Range.dummyRange
       in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____230 ->
        let uu____233 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____233
  
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name [@@deriving show]
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____250 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____262 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____274 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences : 'Auu____285 . Prims.unit -> 'Auu____285 Prims.list =
  fun uu____288  -> [] 
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
  fun uu____377  ->
    fun k  -> match uu____377 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____406  ->
    fun k  ->
      fun v1  -> match uu____406 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____428  -> match uu____428 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : Prims.unit -> dependence_graph) =
  fun uu____444  ->
    let uu____445 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____445
  
let (empty_deps : deps) =
  let uu____456 =
    let uu____465 = deps_empty ()  in
    let uu____466 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____465, uu____466, [])  in
  Mk uu____456 
let (all_cmd_line_files : deps -> Prims.string Prims.list) =
  fun uu____501  ->
    match uu____501 with | Mk (uu____504,uu____505,fns) -> fns
  
let (module_name_of_dep : dependence -> module_name) =
  fun uu___54_513  ->
    match uu___54_513 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____527 = FStar_Util.smap_try_find file_system_map key  in
      match uu____527 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____549) ->
          let uu____564 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____564
      | FStar_Pervasives_Native.Some
          (uu____565,FStar_Pervasives_Native.Some fn) ->
          let uu____581 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____581
      | uu____582 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____603 = FStar_Util.smap_try_find file_system_map key  in
      match uu____603 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____625) ->
          FStar_Pervasives_Native.Some iface
      | uu____640 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____661 = FStar_Util.smap_try_find file_system_map key  in
      match uu____661 with
      | FStar_Pervasives_Native.Some
          (uu____682,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____698 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____715 = interface_of file_system_map key  in
      FStar_Option.isSome uu____715
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____724 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____724
  
let (check_or_use_extracted_interface :
  Prims.string Prims.list -> Prims.string -> Prims.bool) =
  fun all_cmd_line_files1  ->
    fun fn  ->
      let uu____737 = is_interface fn  in
      if uu____737
      then false
      else
        (let is_cmd_line_fn = FStar_List.contains fn all_cmd_line_files1  in
         (FStar_Options.check_interface ()) ||
           ((FStar_Options.use_extracted_interfaces ()) &&
              (Prims.op_Negation is_cmd_line_fn)))
  
let (cache_file_name :
  Prims.string Prims.list -> Prims.string -> Prims.string) =
  fun all_cmd_line_files1  ->
    fun fn  ->
      let fn1 =
        let uu____751 =
          let uu____752 = FStar_Options.dep ()  in
          uu____752 <> FStar_Pervasives_Native.None  in
        if uu____751
        then fn
        else
          (let uu____758 =
             check_or_use_extracted_interface all_cmd_line_files1 fn  in
           if uu____758 then interface_filename fn else fn)
         in
      let uu____760 =
        let uu____761 = FStar_Options.lax ()  in
        if uu____761
        then Prims.strcat fn1 ".checked.lax"
        else Prims.strcat fn1 ".checked"  in
      FStar_Options.prepend_cache_dir uu____760
  
let (file_of_dep_aux :
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name)
  =
  fun use_checked_file  ->
    fun file_system_map  ->
      fun all_cmd_line_files1  ->
        fun d  ->
          let cmd_line_has_impl key =
            FStar_All.pipe_right all_cmd_line_files1
              (FStar_Util.for_some
                 (fun fn  ->
                    (is_implementation fn) &&
                      (let uu____788 = lowercase_module_name fn  in
                       key = uu____788)))
             in
          let maybe_add_suffix f =
            if use_checked_file
            then
              let uu____793 =
                let uu____794 =
                  (let uu____797 = FStar_Options.dep ()  in
                   uu____797 <> FStar_Pervasives_Native.None) &&
                    (FStar_Options.use_extracted_interfaces ())
                   in
                if uu____794 then interface_filename f else f  in
              cache_file_name all_cmd_line_files1 uu____793
            else f  in
          match d with
          | UseInterface key ->
              let uu____805 = interface_of file_system_map key  in
              (match uu____805 with
               | FStar_Pervasives_Native.None  ->
                   let uu____811 =
                     let uu____816 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____816)  in
                   FStar_Errors.raise_err uu____811
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____820 =
                (cmd_line_has_impl key) &&
                  (let uu____822 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____822)
                 in
              if uu____820
              then
                let uu____825 = FStar_Options.expose_interfaces ()  in
                (if uu____825
                 then
                   let uu____826 =
                     let uu____827 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____827  in
                   maybe_add_suffix uu____826
                 else
                   (let uu____831 =
                      let uu____836 =
                        let uu____837 =
                          let uu____838 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____838  in
                        let uu____841 =
                          let uu____842 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____842  in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____837 uu____841
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____836)
                       in
                    FStar_Errors.raise_err uu____831))
              else
                (let uu____846 =
                   let uu____847 = interface_of file_system_map key  in
                   FStar_Option.get uu____847  in
                 maybe_add_suffix uu____846)
          | PreferInterface key ->
              let uu____851 = implementation_of file_system_map key  in
              (match uu____851 with
               | FStar_Pervasives_Native.None  ->
                   let uu____857 =
                     let uu____862 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____862)
                      in
                   FStar_Errors.raise_err uu____857
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____865 = implementation_of file_system_map key  in
              (match uu____865 with
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
      fun all_cmd_line_files1  ->
        fun fn  ->
          let uu____906 = deps_try_find deps fn  in
          match uu____906 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____920) ->
              FStar_List.map
                (file_of_dep file_system_map all_cmd_line_files1) deps1
  
let (add_dependence :
  dependence_graph -> file_name -> file_name -> Prims.unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____951 to_1 =
          match uu____951 with
          | (d,color) ->
              let uu____971 = is_interface to_1  in
              if uu____971
              then
                let uu____978 =
                  let uu____981 =
                    let uu____982 = lowercase_module_name to_1  in
                    PreferInterface uu____982  in
                  uu____981 :: d  in
                (uu____978, color)
              else
                (let uu____986 =
                   let uu____989 =
                     let uu____990 = lowercase_module_name to_1  in
                     UseImplementation uu____990  in
                   uu____989 :: d  in
                 (uu____986, color))
           in
        let uu____993 = deps_try_find deps from  in
        match uu____993 with
        | FStar_Pervasives_Native.None  ->
            let uu____1004 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____1004
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____1020 = add_dep key_deps to_  in
            deps_add_dep deps from uu____1020
  
let (print_graph : dependence_graph -> Prims.unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1031 =
       let uu____1032 =
         let uu____1033 =
           let uu____1034 =
             let uu____1037 =
               let uu____1040 = deps_keys graph  in
               FStar_List.unique uu____1040  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1049 =
                      let uu____1054 = deps_try_find graph k  in
                      FStar_Util.must uu____1054  in
                    FStar_Pervasives_Native.fst uu____1049  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1037
              in
           FStar_String.concat "\n" uu____1034  in
         Prims.strcat uu____1033 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1032  in
     FStar_Util.write_file "dep.graph" uu____1031)
  
let (build_inclusion_candidates_list :
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1083  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1100 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1100  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1126 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1126
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1147 =
              let uu____1152 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1152)  in
            FStar_Errors.raise_err uu____1147)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1192 = FStar_Util.smap_try_find map1 key  in
      match uu____1192 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1229 = is_interface full_path  in
          if uu____1229
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1263 = is_interface full_path  in
          if uu____1263
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1290 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1304  ->
          match uu____1304 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1290);
    FStar_List.iter
      (fun f  ->
         let uu____1315 = lowercase_module_name f  in add_entry uu____1315 f)
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
        (let uu____1330 =
           let uu____1333 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1333  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1359 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1359  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1330);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1493 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1493 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1504 = string_of_lid l last1  in
      FStar_String.lowercase uu____1504
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1508 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1508
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> Prims.unit) =
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
        let uu____1525 =
          let uu____1530 =
            let uu____1531 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1531 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1530)  in
        FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____1525
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1536 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1550 = FStar_Options.prims_basename ()  in
      let uu____1551 =
        let uu____1554 = FStar_Options.pervasives_basename ()  in
        let uu____1555 =
          let uu____1558 = FStar_Options.pervasives_native_basename ()  in
          [uu____1558]  in
        uu____1554 :: uu____1555  in
      uu____1550 :: uu____1551  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1593 =
         let uu____1596 = lowercase_module_name full_filename  in
         namespace_of_module uu____1596  in
       match uu____1593 with
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
        let uu____1785 =
          let uu____1786 =
            let uu____1787 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (fun d'  -> d' = d) uu____1787  in
          Prims.op_Negation uu____1786  in
        if uu____1785
        then
          let uu____1857 =
            let uu____1860 = FStar_ST.op_Bang deps1  in d :: uu____1860  in
          FStar_ST.op_Colon_Equals deps1 uu____1857
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2021 = resolve_module_name original_or_working_map key  in
        match uu____2021 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2060 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____2062 = FStar_Options.dep ()  in
                   uu____2062 = (FStar_Pervasives_Native.Some "full"))
                 in
              if uu____2060
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2101 -> false  in
      let record_open_module let_open lid =
        let uu____2111 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2111
        then true
        else
          (if let_open
           then
             (let uu____2114 =
                let uu____2119 =
                  let uu____2120 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2120  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2119)
                 in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2114)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2128 =
            let uu____2133 =
              let uu____2134 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2134
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2133)
             in
          FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2128
        else ()  in
      let record_open let_open lid =
        let uu____2143 = record_open_module let_open lid  in
        if uu____2143
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2153 =
        match uu____2153 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2160 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident)  in
        let alias = lowercase_join_longident lid true  in
        let uu____2170 = FStar_Util.smap_try_find original_map alias  in
        match uu____2170 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2224 =
                let uu____2229 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2229)
                 in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2224);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2234 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2238 = add_dependence_edge working_map module_name  in
            if uu____2238
            then ()
            else
              (let uu____2240 = FStar_Options.debug_any ()  in
               if uu____2240
               then
                 let uu____2241 =
                   let uu____2246 =
                     let uu____2247 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2247
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2246)
                    in
                 FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                   uu____2241
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___55_2333 =
         match uu___55_2333 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2342 =
                   let uu____2343 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2343  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2347) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2354 =
                   let uu____2355 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2355  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___56_2364 =
         match uu___56_2364 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2369 = record_module_alias ident lid  in
             if uu____2369
             then
               let uu____2370 =
                 let uu____2371 = lowercase_join_longident lid true  in
                 PreferInterface uu____2371  in
               add_dep deps uu____2370
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2406,patterms) ->
             FStar_List.iter
               (fun uu____2428  ->
                  match uu____2428 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2437,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2439;
               FStar_Parser_AST.mdest = uu____2440;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2442;
               FStar_Parser_AST.mdest = uu____2443;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2445,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2447;
               FStar_Parser_AST.mdest = uu____2448;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2452,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2482  -> match uu____2482 with | (x,docnik) -> x)
                 ts
                in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2495,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2502 -> ()
         | FStar_Parser_AST.Pragma uu____2503 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2539 =
                 let uu____2540 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2540 > (Prims.parse_int "1")  in
               if uu____2539
               then
                 let uu____2582 =
                   let uu____2587 =
                     let uu____2588 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2588
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2587)  in
                 FStar_Errors.raise_error uu____2582
                   (FStar_Ident.range_of_lid lid)
               else ()))
       
       and collect_tycon uu___57_2590 =
         match uu___57_2590 with
         | FStar_Parser_AST.TyconAbstract (uu____2591,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2603,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2617,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2663  ->
                   match uu____2663 with
                   | (uu____2672,t,uu____2674) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2679,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2738  ->
                   match uu____2738 with
                   | (uu____2751,t,uu____2753,uu____2754) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___58_2763 =
         match uu___58_2763 with
         | FStar_Parser_AST.DefineEffect (uu____2764,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2778,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___59_2789 =
         match uu___59_2789 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2790,t);
             FStar_Parser_AST.brange = uu____2792;
             FStar_Parser_AST.blevel = uu____2793;
             FStar_Parser_AST.aqual = uu____2794;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2795,t);
             FStar_Parser_AST.brange = uu____2797;
             FStar_Parser_AST.blevel = uu____2798;
             FStar_Parser_AST.aqual = uu____2799;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2801;
             FStar_Parser_AST.blevel = uu____2802;
             FStar_Parser_AST.aqual = uu____2803;_} -> collect_term t
         | uu____2804 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___60_2806 =
         match uu___60_2806 with
         | FStar_Const.Const_int
             (uu____2807,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____2822 =
               let uu____2823 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____2823  in
             add_dep deps uu____2822
         | FStar_Const.Const_char uu____2857 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____2891 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____2925 -> ()
       
       and collect_term' uu___61_2926 =
         match uu___61_2926 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____2935 =
                   let uu____2936 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____2936  in
                 collect_term' uu____2935)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____2938 -> ()
         | FStar_Parser_AST.Uvar uu____2939 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____2942) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____2972  ->
                   match uu____2972 with | (t,uu____2978) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____2988) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____2990,patterms,t) ->
             (FStar_List.iter
                (fun uu____3040  ->
                   match uu____3040 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3069 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3080,t1,t2) ->
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
                (fun uu____3176  ->
                   match uu____3176 with | (uu____3181,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3184) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3240,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3244) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3250) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3256,uu____3257) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___62_3265 =
         match uu___62_3265 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3266 -> ()
         | FStar_Parser_AST.PatConst uu____3267 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3275 -> ()
         | FStar_Parser_AST.PatName uu____3282 -> ()
         | FStar_Parser_AST.PatTvar uu____3283 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3297) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3316  ->
                  match uu____3316 with | (uu____3321,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3345 =
         match uu____3345 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3363 = FStar_Parser_Driver.parse_file filename  in
       match uu____3363 with
       | (ast,uu____3383) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3398 =
               ((is_interface filename) &&
                  (has_implementation original_map mname))
                 &&
                 (let uu____3400 = FStar_Options.dep ()  in
                  uu____3400 = (FStar_Pervasives_Native.Some "full"))
                in
             if uu____3398
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3440 = FStar_ST.op_Bang deps  in
             let uu____3488 = FStar_ST.op_Bang mo_roots  in
             (uu____3440, uu____3488))))
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files1  ->
    let all_cmd_line_files2 =
      FStar_All.pipe_right all_cmd_line_files1
        (FStar_List.map
           (fun fn  ->
              let uu____3570 = FStar_Options.find_file fn  in
              match uu____3570 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3573 =
                    let uu____3578 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3578)  in
                  FStar_Errors.raise_err uu____3573
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files2  in
    let rec discover_one file_name =
      let uu____3586 =
        let uu____3587 = deps_try_find dep_graph file_name  in
        uu____3587 = FStar_Pervasives_Native.None  in
      if uu____3586
      then
        let uu____3604 = collect_one file_system_map file_name  in
        match uu____3604 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____3627 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____3627
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____3632 =
                let uu____3637 = FStar_List.unique deps1  in
                (uu____3637, White)  in
              deps_add_dep dep_graph file_name uu____3632);
             (let uu____3642 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files2)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____3642))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files2;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec aux cycle filename =
         let uu____3675 =
           let uu____3680 = deps_try_find dep_graph filename  in
           FStar_Util.must uu____3680  in
         match uu____3675 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  ((let uu____3694 =
                      let uu____3699 =
                        FStar_Util.format1
                          "Recursive dependency on module %s\n" filename
                         in
                      (FStar_Errors.Warning_RecursiveDependency, uu____3699)
                       in
                    FStar_Errors.log_issue FStar_Range.dummyRange uu____3694);
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____3705 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3705);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3711 =
                      let uu____3714 = FStar_ST.op_Bang topologically_sorted
                         in
                      filename :: uu____3714  in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3711)))
          in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted  in
     FStar_All.pipe_right all_cmd_line_files2
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let uu____3860 = topological_dependences_of all_cmd_line_files2  in
      (uu____3860, (Mk (dep_graph, file_system_map, all_cmd_line_files2)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____3873  ->
    fun f  ->
      match uu____3873 with
      | Mk (deps,file_system_map,all_cmd_line_files1) ->
          dependences_of file_system_map deps all_cmd_line_files1 f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____3898  ->
    fun fn  ->
      match uu____3898 with
      | Mk (deps,file_system_map,all_cmd_line_files1) ->
          let fn1 =
            let uu____3916 = FStar_Options.find_file fn  in
            match uu____3916 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____3920 -> fn  in
          let cache_file = cache_file_name all_cmd_line_files1 fn1  in
          let digest_of_file1 fn2 =
            (let uu____3929 = FStar_Options.debug_any ()  in
             if uu____3929
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____3940 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____3940
            then
              let uu____3947 =
                let uu____3952 =
                  let uu____3953 =
                    let uu____3954 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____3954  in
                  digest_of_file1 uu____3953  in
                ("interface", uu____3952)  in
              [uu____3947]
            else []  in
          let binary_deps =
            let uu____3973 =
              dependences_of file_system_map deps all_cmd_line_files1 fn1  in
            FStar_All.pipe_right uu____3973
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____3983 =
                      (is_interface fn2) &&
                        (let uu____3985 = lowercase_module_name fn2  in
                         uu____3985 = module_name)
                       in
                    Prims.op_Negation uu____3983))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____3995 = lowercase_module_name fn11  in
                   let uu____3996 = lowercase_module_name fn2  in
                   FStar_String.compare uu____3995 uu____3996) binary_deps
             in
          let rec hash_deps out uu___63_4019 =
            match uu___63_4019 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name all_cmd_line_files1 fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4063 =
                    let uu____4070 =
                      let uu____4075 = lowercase_module_name fn2  in
                      let uu____4076 = digest_of_file1 cache_fn  in
                      (uu____4075, uu____4076)  in
                    uu____4070 :: out  in
                  hash_deps uu____4063 deps1
                else
                  ((let uu____4083 = FStar_Options.debug_any ()  in
                    if uu____4083
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
    let uu____4110 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4129  ->
              match uu____4129 with
              | (m,d) ->
                  let uu____4136 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4136))
       in
    FStar_All.pipe_right uu____4110 (FStar_String.concat "\n")
  
let (print_make : deps -> Prims.unit) =
  fun uu____4141  ->
    match uu____4141 with
    | Mk (deps,file_system_map,all_cmd_line_files1) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4161 =
                  let uu____4166 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4166 FStar_Option.get  in
                match uu____4161 with
                | (f_deps,uu____4188) ->
                    let files =
                      FStar_List.map
                        (file_of_dep file_system_map all_cmd_line_files1)
                        f_deps
                       in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files
                       in
                    FStar_Util.print2 "%s: %s\n\n" f
                      (FStar_String.concat " " files1)))
  
let (print_full : deps -> Prims.unit) =
  fun uu____4200  ->
    match uu____4200 with
    | Mk (deps,file_system_map,all_cmd_line_files1) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____4237 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____4237) ||
              (let uu____4241 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____4241)
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
                let uu____4264 =
                  let uu____4267 = FStar_ST.op_Bang order  in ml_file ::
                    uu____4267
                   in
                FStar_ST.op_Colon_Equals order uu____4264
             in
          let rec aux uu___64_4365 =
            match uu___64_4365 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____4381 = deps_try_find deps file_name  in
                      (match uu____4381 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____4392 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____4392
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____4394) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____4405 = should_visit lc_module_name  in
                  if uu____4405
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____4410 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____4410);
                     (let uu____4414 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____4414);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____4422 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____4422)
           in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____4481 =
              let uu____4482 =
                let uu____4485 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____4485  in
              FStar_Option.get uu____4482  in
            FStar_Util.replace_chars uu____4481 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____4496 = output_file ".ml" f  in norm_path uu____4496  in
        let output_krml_file f =
          let uu____4501 = output_file ".krml" f  in norm_path uu____4501  in
        let output_cmx_file f =
          let uu____4506 = output_file ".cmx" f  in norm_path uu____4506  in
        let cache_file f =
          let uu____4511 = cache_file_name all_cmd_line_files1 f  in
          norm_path uu____4511  in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4534 =
                   let uu____4539 = deps_try_find deps f  in
                   FStar_All.pipe_right uu____4539 FStar_Option.get  in
                 match uu____4534 with
                 | (f_deps,uu____4561) ->
                     let norm_f = norm_path f  in
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files1) f_deps
                        in
                     let files1 = FStar_List.map norm_path files  in
                     let files2 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files1
                        in
                     let files3 = FStar_String.concat "\\\n\t" files2  in
                     ((let uu____4577 = is_interface f  in
                       if uu____4577
                       then
                         let uu____4578 =
                           let uu____4579 =
                             FStar_Options.prepend_cache_dir norm_f  in
                           norm_path uu____4579  in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____4578 norm_f files3
                       else ());
                      (let uu____4582 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4582
                         norm_f files3);
                      (let uu____4584 =
                         ((FStar_Options.use_extracted_interfaces ()) &&
                            (is_implementation f))
                           &&
                           (let uu____4586 =
                              let uu____4587 = lowercase_module_name f  in
                              has_interface file_system_map uu____4587  in
                            Prims.op_Negation uu____4586)
                          in
                       if uu____4584
                       then
                         let uu____4588 =
                           let uu____4589 = interface_filename f  in
                           cache_file uu____4589  in
                         FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4588
                           norm_f files3
                       else ());
                      (let uu____4591 = is_implementation f  in
                       if uu____4591
                       then
                         ((let uu____4593 = output_ml_file f  in
                           let uu____4594 = cache_file f  in
                           FStar_Util.print2 "%s: %s\n\n" uu____4593
                             uu____4594);
                          (let cmx_files =
                             let fst_files =
                               FStar_All.pipe_right f_deps
                                 (FStar_List.map
                                    (file_of_dep_aux false file_system_map
                                       all_cmd_line_files1))
                                in
                             let extracted_fst_files =
                               FStar_All.pipe_right fst_files
                                 (FStar_List.filter
                                    (fun df  ->
                                       (let uu____4616 =
                                          lowercase_module_name df  in
                                        let uu____4617 =
                                          lowercase_module_name f  in
                                        uu____4616 <> uu____4617) &&
                                         (let uu____4619 =
                                            lowercase_module_name df  in
                                          FStar_Options.should_extract
                                            uu____4619)))
                                in
                             FStar_All.pipe_right extracted_fst_files
                               (FStar_List.map output_cmx_file)
                              in
                           (let uu____4625 =
                              let uu____4626 = lowercase_module_name f  in
                              FStar_Options.should_extract uu____4626  in
                            if uu____4625
                            then
                              let uu____4627 = output_cmx_file f  in
                              let uu____4628 = output_ml_file f  in
                              FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                uu____4627 uu____4628
                                (FStar_String.concat "\\\n\t" cmx_files)
                            else ());
                           (let uu____4630 = output_krml_file f  in
                            let uu____4631 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____4630
                              uu____4631)))
                       else
                         (let uu____4633 =
                            (let uu____4636 =
                               let uu____4637 = lowercase_module_name f  in
                               has_implementation file_system_map uu____4637
                                in
                             Prims.op_Negation uu____4636) &&
                              (is_interface f)
                             in
                          if uu____4633
                          then
                            let uu____4638 = output_krml_file f  in
                            let uu____4639 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____4638
                              uu____4639
                          else ())))));
         (let all_fst_files =
            let uu____4644 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____4644
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____4670 = FStar_Options.should_extract mname  in
                    if uu____4670
                    then
                      let uu____4671 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____4671
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____4687 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____4687));
            sort_output_files krml_file_map  in
          (let uu____4689 =
             let uu____4690 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____4690 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____4689);
          (let uu____4700 =
             let uu____4701 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____4701 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____4700);
          (let uu____4710 =
             let uu____4711 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____4711 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____4710)))
  
let (print : deps -> Prims.unit) =
  fun deps  ->
    let uu____4723 = FStar_Options.dep ()  in
    match uu____4723 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4726 = deps  in
        (match uu____4726 with
         | Mk (deps1,uu____4728,uu____4729) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4734 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  