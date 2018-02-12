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
  fun uu___52_165  ->
    match uu___52_165 with
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
  fun uu___53_513  ->
    match uu___53_513 with
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
         ((FStar_Options.use_extracted_interfaces ()) &&
            (Prims.op_Negation is_cmd_line_fn))
           || ((FStar_Options.check_interface ()) && is_cmd_line_fn))
  
let (cache_file_name :
  Prims.string Prims.list -> Prims.string -> Prims.string) =
  fun all_cmd_line_files1  ->
    fun fn  ->
      let fn1 =
        let uu____751 =
          check_or_use_extracted_interface all_cmd_line_files1 fn  in
        if uu____751 then interface_filename fn else fn  in
      let uu____753 =
        let uu____754 = FStar_Options.lax ()  in
        if uu____754
        then Prims.strcat fn1 ".checked.lax"
        else Prims.strcat fn1 ".checked"  in
      FStar_Options.prepend_cache_dir uu____753
  
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
                      (let uu____781 = lowercase_module_name fn  in
                       key = uu____781)))
             in
          let maybe_add_suffix f =
            if use_checked_file
            then cache_file_name all_cmd_line_files1 f
            else f  in
          match d with
          | UseInterface key ->
              let uu____788 = interface_of file_system_map key  in
              (match uu____788 with
               | FStar_Pervasives_Native.None  ->
                   let uu____794 =
                     let uu____799 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____799)  in
                   FStar_Errors.raise_err uu____794
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____803 =
                (cmd_line_has_impl key) &&
                  (let uu____805 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____805)
                 in
              if uu____803
              then
                let uu____808 = FStar_Options.expose_interfaces ()  in
                (if uu____808
                 then
                   let uu____809 =
                     let uu____810 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____810  in
                   maybe_add_suffix uu____809
                 else
                   (let uu____814 =
                      let uu____819 =
                        let uu____820 =
                          let uu____821 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____821  in
                        let uu____824 =
                          let uu____825 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____825  in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____820 uu____824
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____819)
                       in
                    FStar_Errors.raise_err uu____814))
              else
                (let uu____829 =
                   let uu____830 = interface_of file_system_map key  in
                   FStar_Option.get uu____830  in
                 maybe_add_suffix uu____829)
          | PreferInterface key ->
              let uu____834 = implementation_of file_system_map key  in
              (match uu____834 with
               | FStar_Pervasives_Native.None  ->
                   let uu____840 =
                     let uu____845 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____845)
                      in
                   FStar_Errors.raise_err uu____840
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____848 = implementation_of file_system_map key  in
              (match uu____848 with
               | FStar_Pervasives_Native.None  ->
                   let uu____854 =
                     let uu____859 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____859)
                      in
                   FStar_Errors.raise_err uu____854
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
          let uu____889 = deps_try_find deps fn  in
          match uu____889 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____903) ->
              FStar_List.map
                (file_of_dep file_system_map all_cmd_line_files1) deps1
  
let (add_dependence :
  dependence_graph -> file_name -> file_name -> Prims.unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____934 to_1 =
          match uu____934 with
          | (d,color) ->
              let uu____954 = is_interface to_1  in
              if uu____954
              then
                let uu____961 =
                  let uu____964 =
                    let uu____965 = lowercase_module_name to_1  in
                    PreferInterface uu____965  in
                  uu____964 :: d  in
                (uu____961, color)
              else
                (let uu____969 =
                   let uu____972 =
                     let uu____973 = lowercase_module_name to_1  in
                     UseImplementation uu____973  in
                   uu____972 :: d  in
                 (uu____969, color))
           in
        let uu____976 = deps_try_find deps from  in
        match uu____976 with
        | FStar_Pervasives_Native.None  ->
            let uu____987 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____987
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____1003 = add_dep key_deps to_  in
            deps_add_dep deps from uu____1003
  
let (print_graph : dependence_graph -> Prims.unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1014 =
       let uu____1015 =
         let uu____1016 =
           let uu____1017 =
             let uu____1020 =
               let uu____1023 = deps_keys graph  in
               FStar_List.unique uu____1023  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1032 =
                      let uu____1037 = deps_try_find graph k  in
                      FStar_Util.must uu____1037  in
                    FStar_Pervasives_Native.fst uu____1032  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1020
              in
           FStar_String.concat "\n" uu____1017  in
         Prims.strcat uu____1016 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1015  in
     FStar_Util.write_file "dep.graph" uu____1014)
  
let (build_inclusion_candidates_list :
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1066  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1083 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1083  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1109 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1109
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1130 =
              let uu____1135 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1135)  in
            FStar_Errors.raise_err uu____1130)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1175 = FStar_Util.smap_try_find map1 key  in
      match uu____1175 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1212 = is_interface full_path  in
          if uu____1212
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1246 = is_interface full_path  in
          if uu____1246
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1273 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1287  ->
          match uu____1287 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1273);
    FStar_List.iter
      (fun f  ->
         let uu____1298 = lowercase_module_name f  in add_entry uu____1298 f)
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
        (let uu____1313 =
           let uu____1316 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1316  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1342 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1342  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1313);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1580 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1580 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1591 = string_of_lid l last1  in
      FStar_String.lowercase uu____1591
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1595 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1595
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> Prims.unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1605 =
        let uu____1606 =
          let uu____1607 =
            let uu____1608 =
              let uu____1611 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1611  in
            FStar_Util.must uu____1608  in
          FStar_String.lowercase uu____1607  in
        uu____1606 <> k'  in
      if uu____1605
      then
        let uu____1612 =
          let uu____1617 =
            let uu____1618 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1618 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1617)  in
        FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____1612
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1623 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1637 = FStar_Options.prims_basename ()  in
      let uu____1638 =
        let uu____1641 = FStar_Options.pervasives_basename ()  in
        let uu____1642 =
          let uu____1645 = FStar_Options.pervasives_native_basename ()  in
          [uu____1645]  in
        uu____1641 :: uu____1642  in
      uu____1637 :: uu____1638  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1680 =
         let uu____1683 = lowercase_module_name full_filename  in
         namespace_of_module uu____1683  in
       match uu____1680 with
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
        let uu____1924 =
          let uu____1925 =
            let uu____1926 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (fun d'  -> d' = d) uu____1926  in
          Prims.op_Negation uu____1925  in
        if uu____1924
        then
          let uu____2048 =
            let uu____2051 = FStar_ST.op_Bang deps1  in d :: uu____2051  in
          FStar_ST.op_Colon_Equals deps1 uu____2048
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2316 = resolve_module_name original_or_working_map key  in
        match uu____2316 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2433 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____2435 = FStar_Options.dep ()  in
                   uu____2435 = (FStar_Pervasives_Native.Some "full"))
                 in
              if uu____2433
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2552 -> false  in
      let record_open_module let_open lid =
        let uu____2562 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2562
        then true
        else
          (if let_open
           then
             (let uu____2565 =
                let uu____2570 =
                  let uu____2571 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2571  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2570)
                 in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2565)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2579 =
            let uu____2584 =
              let uu____2585 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2585
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2584)
             in
          FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2579
        else ()  in
      let record_open let_open lid =
        let uu____2594 = record_open_module let_open lid  in
        if uu____2594
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2604 =
        match uu____2604 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2611 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident)  in
        let alias = lowercase_join_longident lid true  in
        let uu____2621 = FStar_Util.smap_try_find original_map alias  in
        match uu____2621 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2675 =
                let uu____2680 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2680)
                 in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2675);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2685 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2689 = add_dependence_edge working_map module_name  in
            if uu____2689
            then ()
            else
              (let uu____2691 = FStar_Options.debug_any ()  in
               if uu____2691
               then
                 let uu____2692 =
                   let uu____2697 =
                     let uu____2698 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2698
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2697)
                    in
                 FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                   uu____2692
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___54_2784 =
         match uu___54_2784 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2793 =
                   let uu____2794 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2794  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2798) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2805 =
                   let uu____2806 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2806  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___55_2815 =
         match uu___55_2815 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2820 = record_module_alias ident lid  in
             if uu____2820
             then
               let uu____2821 =
                 let uu____2822 = lowercase_join_longident lid true  in
                 PreferInterface uu____2822  in
               add_dep deps uu____2821
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2935,patterms) ->
             FStar_List.iter
               (fun uu____2957  ->
                  match uu____2957 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2966,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2968;
               FStar_Parser_AST.mdest = uu____2969;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2971;
               FStar_Parser_AST.mdest = uu____2972;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2974,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2976;
               FStar_Parser_AST.mdest = uu____2977;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2981,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____3011  -> match uu____3011 with | (x,docnik) -> x)
                 ts
                in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____3024,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____3031 -> ()
         | FStar_Parser_AST.Pragma uu____3032 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____3146 =
                 let uu____3147 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____3147 > (Prims.parse_int "1")  in
               if uu____3146
               then
                 let uu____3241 =
                   let uu____3246 =
                     let uu____3247 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____3247
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____3246)  in
                 FStar_Errors.raise_error uu____3241
                   (FStar_Ident.range_of_lid lid)
               else ()))
       
       and collect_tycon uu___56_3249 =
         match uu___56_3249 with
         | FStar_Parser_AST.TyconAbstract (uu____3250,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____3262,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____3276,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3322  ->
                   match uu____3322 with
                   | (uu____3331,t,uu____3333) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3338,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3397  ->
                   match uu____3397 with
                   | (uu____3410,t,uu____3412,uu____3413) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___57_3422 =
         match uu___57_3422 with
         | FStar_Parser_AST.DefineEffect (uu____3423,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3437,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___58_3448 =
         match uu___58_3448 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3449,t);
             FStar_Parser_AST.brange = uu____3451;
             FStar_Parser_AST.blevel = uu____3452;
             FStar_Parser_AST.aqual = uu____3453;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3454,t);
             FStar_Parser_AST.brange = uu____3456;
             FStar_Parser_AST.blevel = uu____3457;
             FStar_Parser_AST.aqual = uu____3458;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3460;
             FStar_Parser_AST.blevel = uu____3461;
             FStar_Parser_AST.aqual = uu____3462;_} -> collect_term t
         | uu____3463 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___59_3465 =
         match uu___59_3465 with
         | FStar_Const.Const_int
             (uu____3466,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3481 =
               let uu____3482 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____3482  in
             add_dep deps uu____3481
         | FStar_Const.Const_char uu____3594 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3706 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3818 -> ()
       
       and collect_term' uu___60_3819 =
         match uu___60_3819 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3828 =
                   let uu____3829 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3829  in
                 collect_term' uu____3828)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3831 -> ()
         | FStar_Parser_AST.Uvar uu____3832 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3835) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3865  ->
                   match uu____3865 with | (t,uu____3871) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3881) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3883,patterms,t) ->
             (FStar_List.iter
                (fun uu____3907  ->
                   match uu____3907 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3918,t1,t2) ->
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
                (fun uu____4014  ->
                   match uu____4014 with | (uu____4019,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____4022) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____4078,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____4081,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____4084) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____4090) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____4096,uu____4097) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___61_4105 =
         match uu___61_4105 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____4106 -> ()
         | FStar_Parser_AST.PatConst uu____4107 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____4115 -> ()
         | FStar_Parser_AST.PatName uu____4122 -> ()
         | FStar_Parser_AST.PatTvar uu____4123 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____4137) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____4156  ->
                  match uu____4156 with | (uu____4161,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____4185 =
         match uu____4185 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____4203 = FStar_Parser_Driver.parse_file filename  in
       match uu____4203 with
       | (ast,uu____4223) ->
           let mname = lowercase_module_name filename  in
           ((let uu____4238 =
               ((is_interface filename) &&
                  (has_implementation original_map mname))
                 &&
                 (let uu____4240 = FStar_Options.dep ()  in
                  uu____4240 = (FStar_Pervasives_Native.Some "full"))
                in
             if uu____4238
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____4358 = FStar_ST.op_Bang deps  in
             let uu____4458 = FStar_ST.op_Bang mo_roots  in
             (uu____4358, uu____4458))))
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files1  ->
    let all_cmd_line_files2 =
      FStar_All.pipe_right all_cmd_line_files1
        (FStar_List.map
           (fun fn  ->
              let uu____4592 = FStar_Options.find_file fn  in
              match uu____4592 with
              | FStar_Pervasives_Native.None  ->
                  let uu____4595 =
                    let uu____4600 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____4600)  in
                  FStar_Errors.raise_err uu____4595
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files2  in
    let rec discover_one file_name =
      let uu____4608 =
        let uu____4609 = deps_try_find dep_graph file_name  in
        uu____4609 = FStar_Pervasives_Native.None  in
      if uu____4608
      then
        let uu____4626 = collect_one file_system_map file_name  in
        match uu____4626 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____4649 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____4649
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____4654 =
                let uu____4659 = FStar_List.unique deps1  in
                (uu____4659, White)  in
              deps_add_dep dep_graph file_name uu____4654);
             (let uu____4664 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files2)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____4664))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files2;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec aux cycle filename =
         let uu____4697 =
           let uu____4702 = deps_try_find dep_graph filename  in
           FStar_Util.must uu____4702  in
         match uu____4697 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  ((let uu____4716 =
                      let uu____4721 =
                        FStar_Util.format1
                          "Recursive dependency on module %s\n" filename
                         in
                      (FStar_Errors.Warning_RecursiveDependency, uu____4721)
                       in
                    FStar_Errors.log_issue FStar_Range.dummyRange uu____4716);
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____4727 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4727);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____4733 =
                      let uu____4736 = FStar_ST.op_Bang topologically_sorted
                         in
                      filename :: uu____4736  in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____4733)))
          in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted  in
     FStar_All.pipe_right all_cmd_line_files2
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let uu____5038 = topological_dependences_of all_cmd_line_files2  in
      (uu____5038, (Mk (dep_graph, file_system_map, all_cmd_line_files2)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____5051  ->
    fun f  ->
      match uu____5051 with
      | Mk (deps,file_system_map,all_cmd_line_files1) ->
          dependences_of file_system_map deps all_cmd_line_files1 f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____5076  ->
    fun fn  ->
      match uu____5076 with
      | Mk (deps,file_system_map,all_cmd_line_files1) ->
          let fn1 =
            let uu____5094 = FStar_Options.find_file fn  in
            match uu____5094 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____5098 -> fn  in
          let cache_file = cache_file_name all_cmd_line_files1 fn1  in
          let digest_of_file1 fn2 =
            (let uu____5107 = FStar_Options.debug_any ()  in
             if uu____5107
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____5118 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____5118
            then
              let uu____5125 =
                let uu____5130 =
                  let uu____5131 =
                    let uu____5132 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____5132  in
                  digest_of_file1 uu____5131  in
                ("interface", uu____5130)  in
              [uu____5125]
            else []  in
          let binary_deps =
            let uu____5151 =
              dependences_of file_system_map deps all_cmd_line_files1 fn1  in
            FStar_All.pipe_right uu____5151
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____5161 =
                      (is_interface fn2) &&
                        (let uu____5163 = lowercase_module_name fn2  in
                         uu____5163 = module_name)
                       in
                    Prims.op_Negation uu____5161))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____5173 = lowercase_module_name fn11  in
                   let uu____5174 = lowercase_module_name fn2  in
                   FStar_String.compare uu____5173 uu____5174) binary_deps
             in
          let rec hash_deps out uu___62_5197 =
            match uu___62_5197 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name all_cmd_line_files1 fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____5241 =
                    let uu____5248 =
                      let uu____5253 = lowercase_module_name fn2  in
                      let uu____5254 = digest_of_file1 cache_fn  in
                      (uu____5253, uu____5254)  in
                    uu____5248 :: out  in
                  hash_deps uu____5241 deps1
                else
                  ((let uu____5261 = FStar_Options.debug_any ()  in
                    if uu____5261
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
    let uu____5288 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____5307  ->
              match uu____5307 with
              | (m,d) ->
                  let uu____5314 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____5314))
       in
    FStar_All.pipe_right uu____5288 (FStar_String.concat "\n")
  
let (print_make : deps -> Prims.unit) =
  fun uu____5319  ->
    match uu____5319 with
    | Mk (deps,file_system_map,all_cmd_line_files1) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____5339 =
                  let uu____5344 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____5344 FStar_Option.get  in
                match uu____5339 with
                | (f_deps,uu____5366) ->
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
  fun uu____5378  ->
    match uu____5378 with
    | Mk (deps,file_system_map,all_cmd_line_files1) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____5415 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____5415) ||
              (let uu____5419 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____5419)
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
                let uu____5442 =
                  let uu____5445 = FStar_ST.op_Bang order  in ml_file ::
                    uu____5445
                   in
                FStar_ST.op_Colon_Equals order uu____5442
             in
          let rec aux uu___63_5647 =
            match uu___63_5647 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____5663 = deps_try_find deps file_name  in
                      (match uu____5663 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____5674 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____5674
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____5676) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____5687 = should_visit lc_module_name  in
                  if uu____5687
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____5692 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____5692);
                     (let uu____5696 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____5696);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____5704 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____5704)
           in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____5815 =
              let uu____5816 =
                let uu____5819 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____5819  in
              FStar_Option.get uu____5816  in
            FStar_Util.replace_chars uu____5815 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____5830 = output_file ".ml" f  in norm_path uu____5830  in
        let output_krml_file f =
          let uu____5835 = output_file ".krml" f  in norm_path uu____5835  in
        let output_cmx_file f =
          let uu____5840 = output_file ".cmx" f  in norm_path uu____5840  in
        let cache_file f =
          let uu____5845 = cache_file_name all_cmd_line_files1 f  in
          norm_path uu____5845  in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____5867 =
                   let uu____5872 = deps_try_find deps f  in
                   FStar_All.pipe_right uu____5872 FStar_Option.get  in
                 match uu____5867 with
                 | (f_deps,uu____5894) ->
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
                     ((let uu____5910 = is_interface f  in
                       if uu____5910
                       then
                         let uu____5911 =
                           let uu____5912 =
                             FStar_Options.prepend_cache_dir norm_f  in
                           norm_path uu____5912  in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____5911 norm_f files3
                       else ());
                      (let uu____5915 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5915
                         norm_f files3);
                      (let uu____5916 = is_implementation f  in
                       if uu____5916
                       then
                         ((let uu____5918 = output_ml_file f  in
                           let uu____5919 = cache_file f  in
                           FStar_Util.print2 "%s: %s\n\n" uu____5918
                             uu____5919);
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
                                       (let uu____5941 =
                                          lowercase_module_name df  in
                                        let uu____5942 =
                                          lowercase_module_name f  in
                                        uu____5941 <> uu____5942) &&
                                         (let uu____5944 =
                                            lowercase_module_name df  in
                                          FStar_Options.should_extract
                                            uu____5944)))
                                in
                             FStar_All.pipe_right extracted_fst_files
                               (FStar_List.map output_cmx_file)
                              in
                           (let uu____5950 =
                              let uu____5951 = lowercase_module_name f  in
                              FStar_Options.should_extract uu____5951  in
                            if uu____5950
                            then
                              let uu____5952 = output_cmx_file f  in
                              let uu____5953 = output_ml_file f  in
                              FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                uu____5952 uu____5953
                                (FStar_String.concat "\\\n\t" cmx_files)
                            else ());
                           (let uu____5955 = output_krml_file f  in
                            let uu____5956 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5955
                              uu____5956)))
                       else
                         (let uu____5958 =
                            (let uu____5961 =
                               let uu____5962 = lowercase_module_name f  in
                               has_implementation file_system_map uu____5962
                                in
                             Prims.op_Negation uu____5961) &&
                              (is_interface f)
                             in
                          if uu____5958
                          then
                            let uu____5963 = output_krml_file f  in
                            let uu____5964 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5963
                              uu____5964
                          else ())))));
         (let all_fst_files =
            let uu____5969 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____5969
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5995 = FStar_Options.should_extract mname  in
                    if uu____5995
                    then
                      let uu____5996 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____5996
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____6012 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____6012));
            sort_output_files krml_file_map  in
          (let uu____6014 =
             let uu____6015 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____6015 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____6014);
          (let uu____6025 =
             let uu____6026 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____6026 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____6025);
          (let uu____6035 =
             let uu____6036 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____6036 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____6035)))
  
let (print : deps -> Prims.unit) =
  fun deps  ->
    let uu____6048 = FStar_Options.dep ()  in
    match uu____6048 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____6051 = deps  in
        (match uu____6051 with
         | Mk (deps1,uu____6053,uu____6054) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____6059 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  