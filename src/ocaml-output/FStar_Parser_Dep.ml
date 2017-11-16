open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut[@@deriving show]
let uu___is_VerifyAll: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____4 -> false
let uu___is_VerifyUserList: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____8 -> false
let uu___is_VerifyFigureItOut: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____12 -> false
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White
  | Gray
  | Black[@@deriving show]
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____26 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____30 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____34 -> false
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____38 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____42 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____68 =
             (l > lext) &&
               (let uu____80 = FStar_String.substring f (l - lext) lext in
                uu____80 = ext) in
           if uu____68
           then
             let uu____97 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____97
           else FStar_Pervasives_Native.None) suffixes in
    let uu____109 = FStar_List.filter FStar_Util.is_some matches in
    match uu____109 with
    | (FStar_Pervasives_Native.Some m)::uu____119 ->
        FStar_Pervasives_Native.Some m
    | uu____126 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____134 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____134 = 105
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____138 = is_interface f in Prims.op_Negation uu____138
let list_of_option:
  'Auu____141 .
    'Auu____141 FStar_Pervasives_Native.option -> 'Auu____141 Prims.list
  =
  fun uu___65_149  ->
    match uu___65_149 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____155 .
    ('Auu____155 FStar_Pervasives_Native.option,'Auu____155
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____155 Prims.list
  =
  fun uu____169  ->
    match uu____169 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let module_name_of_file: Prims.string -> Prims.string =
  fun f  ->
    let uu____191 =
      let uu____194 = FStar_Util.basename f in
      check_and_strip_suffix uu____194 in
    match uu____191 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____196 =
          let uu____201 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          (FStar_Errors.NotValidFStarFile, uu____201) in
        FStar_Errors.raise_err uu____196
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____205 = module_name_of_file f in FStar_String.lowercase uu____205
let namespace_of_module:
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun f  ->
    let lid =
      FStar_Ident.lid_of_path (FStar_Ident.path_of_text f)
        FStar_Range.dummyRange in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____214 ->
        let uu____217 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
        FStar_Pervasives_Native.Some uu____217
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____234 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____246 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____258 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____269 . Prims.unit -> 'Auu____269 Prims.list =
  fun uu____272  -> []
type dependence_graph =
  | Deps of (dependences,color) FStar_Pervasives_Native.tuple2
  FStar_Util.smap[@@deriving show]
let uu___is_Deps: dependence_graph -> Prims.bool = fun projectee  -> true
let __proj__Deps__item___0:
  dependence_graph ->
    (dependences,color) FStar_Pervasives_Native.tuple2 FStar_Util.smap
  = fun projectee  -> match projectee with | Deps _0 -> _0
type deps =
  | Mk of (dependence_graph,files_for_module_name,file_name Prims.list)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Mk: deps -> Prims.bool = fun projectee  -> true
let __proj__Mk__item___0:
  deps ->
    (dependence_graph,files_for_module_name,file_name Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Mk _0 -> _0
let deps_try_find:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun uu____361  ->
    fun k  -> match uu____361 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____390  ->
    fun k  ->
      fun v1  -> match uu____390 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____412  -> match uu____412 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____428  ->
    let uu____429 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____429
let empty_deps: deps =
  let uu____440 =
    let uu____449 = deps_empty () in
    let uu____450 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____449, uu____450, []) in
  Mk uu____440
let module_name_of_dep: dependence -> module_name =
  fun uu___66_483  ->
    match uu___66_483 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____497 = FStar_Util.smap_try_find file_system_map key in
      match uu____497 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____519) ->
          let uu____534 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____534
      | FStar_Pervasives_Native.Some
          (uu____535,FStar_Pervasives_Native.Some fn) ->
          let uu____551 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____551
      | uu____552 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____573 = FStar_Util.smap_try_find file_system_map key in
      match uu____573 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____595) ->
          FStar_Pervasives_Native.Some iface
      | uu____610 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____631 = FStar_Util.smap_try_find file_system_map key in
      match uu____631 with
      | FStar_Pervasives_Native.Some
          (uu____652,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____668 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____685 = interface_of file_system_map key in
      FStar_Option.isSome uu____685
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____694 = implementation_of file_system_map key in
      FStar_Option.isSome uu____694
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let uu____700 = FStar_Options.lax () in
    if uu____700
    then Prims.strcat fn ".checked.lax"
    else Prims.strcat fn ".checked"
let file_of_dep_aux:
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name
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
                      (let uu____727 = lowercase_module_name fn in
                       key = uu____727))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____734 = interface_of file_system_map key in
              (match uu____734 with
               | FStar_Pervasives_Native.None  ->
                   let uu____740 =
                     let uu____745 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     (FStar_Errors.MissingInterface, uu____745) in
                   FStar_Errors.raise_err uu____740
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file then Prims.strcat f ".source" else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____749 =
                (cmd_line_has_impl key) &&
                  (let uu____751 = FStar_Options.dep () in
                   FStar_Option.isNone uu____751) in
              if uu____749
              then
                let uu____754 = FStar_Options.expose_interfaces () in
                (if uu____754
                 then
                   let uu____755 =
                     let uu____756 = implementation_of file_system_map key in
                     FStar_Option.get uu____756 in
                   maybe_add_suffix uu____755
                 else
                   (let uu____760 =
                      let uu____765 =
                        let uu____766 =
                          let uu____767 =
                            implementation_of file_system_map key in
                          FStar_Option.get uu____767 in
                        let uu____770 =
                          let uu____771 = interface_of file_system_map key in
                          FStar_Option.get uu____771 in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____766 uu____770 in
                      (FStar_Errors.MissingExposeInterfacesOption, uu____765) in
                    FStar_Errors.raise_err uu____760))
              else
                (let uu____775 =
                   let uu____776 = interface_of file_system_map key in
                   FStar_Option.get uu____776 in
                 maybe_add_suffix uu____775)
          | PreferInterface key ->
              let uu____780 = implementation_of file_system_map key in
              (match uu____780 with
               | FStar_Pervasives_Native.None  ->
                   let uu____786 =
                     let uu____791 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.MissingImplementation, uu____791) in
                   FStar_Errors.raise_err uu____786
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____794 = implementation_of file_system_map key in
              (match uu____794 with
               | FStar_Pervasives_Native.None  ->
                   let uu____800 =
                     let uu____805 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.MissingImplementation, uu____805) in
                   FStar_Errors.raise_err uu____800
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
let file_of_dep:
  files_for_module_name -> file_name Prims.list -> dependence -> file_name =
  file_of_dep_aux false
let dependences_of:
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list
  =
  fun file_system_map  ->
    fun deps  ->
      fun all_cmd_line_files  ->
        fun fn  ->
          let uu____835 = deps_try_find deps fn in
          match uu____835 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____849) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____880 to_1 =
          match uu____880 with
          | (d,color) ->
              let uu____900 = is_interface to_1 in
              if uu____900
              then
                let uu____907 =
                  let uu____910 =
                    let uu____911 = lowercase_module_name to_1 in
                    PreferInterface uu____911 in
                  uu____910 :: d in
                (uu____907, color)
              else
                (let uu____915 =
                   let uu____918 =
                     let uu____919 = lowercase_module_name to_1 in
                     UseImplementation uu____919 in
                   uu____918 :: d in
                 (uu____915, color)) in
        let uu____922 = deps_try_find deps from in
        match uu____922 with
        | FStar_Pervasives_Native.None  ->
            let uu____933 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____933
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____949 = add_dep key_deps to_ in
            deps_add_dep deps from uu____949
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____960 =
       let uu____961 =
         let uu____962 =
           let uu____963 =
             let uu____966 =
               let uu____969 = deps_keys graph in FStar_List.unique uu____969 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____978 =
                      let uu____983 = deps_try_find graph k in
                      FStar_Util.must uu____983 in
                    FStar_Pervasives_Native.fst uu____978 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____966 in
           FStar_String.concat "\n" uu____963 in
         Prims.strcat uu____962 "\n}\n" in
       Prims.strcat "digraph {\n" uu____961 in
     FStar_Util.write_file "dep.graph" uu____960)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1010  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____1027 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____1027 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1053 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1053
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1074 =
              let uu____1079 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              (FStar_Errors.NotValidIncludeDirectory, uu____1079) in
            FStar_Errors.raise_err uu____1074)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1119 = FStar_Util.smap_try_find map1 key in
      match uu____1119 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1156 = is_interface full_path in
          if uu____1156
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1190 = is_interface full_path in
          if uu____1190
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1217 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1231  ->
          match uu____1231 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1217);
    FStar_List.iter
      (fun f  ->
         let uu____1242 = lowercase_module_name f in add_entry uu____1242 f)
      filenames;
    map1
let enter_namespace:
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool
  =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____1257 =
           let uu____1260 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1260 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1286 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1286 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1257);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1458 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1458 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1469 = string_of_lid l last1 in
      FStar_String.lowercase uu____1469
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1473 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1473
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1483 =
        let uu____1484 =
          let uu____1485 =
            let uu____1486 =
              let uu____1489 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1489 in
            FStar_Util.must uu____1486 in
          FStar_String.lowercase uu____1485 in
        uu____1484 <> k' in
      if uu____1483
      then
        let uu____1490 =
          let uu____1495 =
            let uu____1496 = string_of_lid lid true in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1496 filename in
          (FStar_Errors.ModuleFileNameMismatch, uu____1495) in
        FStar_Errors.maybe_fatal_error (FStar_Ident.range_of_lid lid)
          uu____1490
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1501 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename in
    let corelibs =
      let uu____1515 = FStar_Options.prims_basename () in
      let uu____1516 =
        let uu____1519 = FStar_Options.pervasives_basename () in
        let uu____1520 =
          let uu____1523 = FStar_Options.pervasives_native_basename () in
          [uu____1523] in
        uu____1519 :: uu____1520 in
      uu____1515 :: uu____1516 in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)] in
       let uu____1558 =
         let uu____1561 = lowercase_module_name full_filename in
         namespace_of_module uu____1561 in
       match uu____1558 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
let collect_one:
  files_for_module_name ->
    Prims.string ->
      (dependence Prims.list,dependence Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun original_map  ->
    fun filename  ->
      let deps = FStar_Util.mk_ref [] in
      let mo_roots = FStar_Util.mk_ref [] in
      let add_dep deps1 d =
        let uu____1964 =
          let uu____1965 =
            let uu____1966 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1966 in
          Prims.op_Negation uu____1965 in
        if uu____1964
        then
          let uu____2117 =
            let uu____2120 = FStar_ST.op_Bang deps1 in d :: uu____2120 in
          FStar_ST.op_Colon_Equals deps1 uu____2117
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true in
        let uu____2443 = resolve_module_name original_or_working_map key in
        match uu____2443 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2470 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name) in
              if uu____2470
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2493 -> false in
      let record_open_module let_open lid =
        let uu____2503 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid)) in
        if uu____2503
        then true
        else
          (if let_open
           then
             (let uu____2506 =
                let uu____2511 =
                  let uu____2512 = string_of_lid lid true in
                  FStar_Util.format1 "Module not found: %s" uu____2512 in
                (FStar_Errors.ModuleOrFileNotFoundWarning, uu____2511) in
              FStar_Errors.maybe_fatal_error (FStar_Ident.range_of_lid lid)
                uu____2506)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2520 =
            let uu____2525 =
              let uu____2526 = string_of_lid lid true in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2526 in
            (FStar_Errors.ModuleOrFileNotFoundWarning, uu____2525) in
          FStar_Errors.maybe_fatal_error (FStar_Ident.range_of_lid lid)
            uu____2520
        else () in
      let record_open let_open lid =
        let uu____2535 = record_open_module let_open lid in
        if uu____2535
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2545 =
        match uu____2545 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2552 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2562 = FStar_Util.smap_try_find original_map alias in
        match uu____2562 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2616 =
                let uu____2621 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias in
                (FStar_Errors.ModuleOrFileNotFoundWarning, uu____2621) in
              FStar_Errors.maybe_fatal_error (FStar_Ident.range_of_lid lid)
                uu____2616);
             false) in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2626 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2630 = add_dependence_edge working_map module_name in
            if uu____2630
            then ()
            else
              (let uu____2632 = FStar_Options.debug_any () in
               if uu____2632
               then
                 let uu____2633 =
                   let uu____2638 =
                     let uu____2639 = FStar_Ident.string_of_lid module_name in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2639 in
                   (FStar_Errors.UnboundModuleReference, uu____2638) in
                 FStar_Errors.maybe_fatal_error
                   (FStar_Ident.range_of_lid lid) uu____2633
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___67_2725 =
         match uu___67_2725 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2734 =
                   let uu____2735 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2735 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2739) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2746 =
                   let uu____2747 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2747 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___68_2756 =
         match uu___68_2756 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2761 = record_module_alias ident lid in
             if uu____2761
             then
               let uu____2762 =
                 let uu____2763 = lowercase_join_longident lid true in
                 PreferInterface uu____2763 in
               add_dep deps uu____2762
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2786,patterms) ->
             FStar_List.iter
               (fun uu____2808  ->
                  match uu____2808 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2817,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2819;
               FStar_Parser_AST.mdest = uu____2820;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2822;
               FStar_Parser_AST.mdest = uu____2823;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2825,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2827;
               FStar_Parser_AST.mdest = uu____2828;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2832,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2862  -> match uu____2862 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2875,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2882 -> ()
         | FStar_Parser_AST.Pragma uu____2883 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2907 =
                 let uu____2908 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2908 > (Prims.parse_int "1") in
               if uu____2907
               then
                 let uu____2969 =
                   let uu____2974 =
                     let uu____2975 = string_of_lid lid true in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2975 in
                   (FStar_Errors.OneModulePerFile, uu____2974) in
                 FStar_Errors.raise_error uu____2969
                   (FStar_Ident.range_of_lid lid)
               else ()))
       and collect_tycon uu___69_2977 =
         match uu___69_2977 with
         | FStar_Parser_AST.TyconAbstract (uu____2978,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2990,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____3004,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3050  ->
                   match uu____3050 with
                   | (uu____3059,t,uu____3061) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3066,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3125  ->
                   match uu____3125 with
                   | (uu____3138,t,uu____3140,uu____3141) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___70_3150 =
         match uu___70_3150 with
         | FStar_Parser_AST.DefineEffect (uu____3151,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3165,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___71_3176 =
         match uu___71_3176 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3177,t);
             FStar_Parser_AST.brange = uu____3179;
             FStar_Parser_AST.blevel = uu____3180;
             FStar_Parser_AST.aqual = uu____3181;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3182,t);
             FStar_Parser_AST.brange = uu____3184;
             FStar_Parser_AST.blevel = uu____3185;
             FStar_Parser_AST.aqual = uu____3186;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3188;
             FStar_Parser_AST.blevel = uu____3189;
             FStar_Parser_AST.aqual = uu____3190;_} -> collect_term t
         | uu____3191 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___72_3193 =
         match uu___72_3193 with
         | FStar_Const.Const_int
             (uu____3194,FStar_Pervasives_Native.Some (signedness,width)) ->
             let u =
               match signedness with
               | FStar_Const.Unsigned  -> "u"
               | FStar_Const.Signed  -> "" in
             let w =
               match width with
               | FStar_Const.Int8  -> "8"
               | FStar_Const.Int16  -> "16"
               | FStar_Const.Int32  -> "32"
               | FStar_Const.Int64  -> "64" in
             let uu____3209 =
               let uu____3210 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3210 in
             add_dep deps uu____3209
         | FStar_Const.Const_char uu____3232 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3254 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3276 -> ()
       and collect_term' uu___73_3277 =
         match uu___73_3277 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3286 =
                   let uu____3287 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3287 in
                 collect_term' uu____3286)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3289 -> ()
         | FStar_Parser_AST.Uvar uu____3290 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3293) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3323  ->
                   match uu____3323 with | (t,uu____3329) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3339) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3341,patterms,t) ->
             (FStar_List.iter
                (fun uu____3365  ->
                   match uu____3365 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3376,t1,t2) ->
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
                (fun uu____3472  ->
                   match uu____3472 with | (uu____3477,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3480) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3536,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3539,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3542) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3548) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3554,uu____3555) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___74_3563 =
         match uu___74_3563 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3564 -> ()
         | FStar_Parser_AST.PatConst uu____3565 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3573 -> ()
         | FStar_Parser_AST.PatName uu____3580 -> ()
         | FStar_Parser_AST.PatTvar uu____3581 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3595) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3614  ->
                  match uu____3614 with | (uu____3619,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3643 =
         match uu____3643 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3661 = FStar_Parser_Driver.parse_file filename in
       match uu____3661 with
       | (ast,uu____3681) ->
           (collect_module ast;
            (let uu____3695 = FStar_ST.op_Bang deps in
             let uu____3762 = FStar_ST.op_Bang mo_roots in
             (uu____3695, uu____3762))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3858 =
        let uu____3859 = deps_try_find dep_graph file_name in
        uu____3859 = FStar_Pervasives_Native.None in
      if uu____3858
      then
        let uu____3876 = collect_one file_system_map file_name in
        match uu____3876 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3899 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3899
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3904 =
                let uu____3909 = FStar_List.unique deps1 in
                (uu____3909, White) in
              deps_add_dep dep_graph file_name uu____3904);
             (let uu____3914 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3914))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3947 =
           let uu____3952 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3952 in
         match uu____3947 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1_warning
                     "Recursive dependency on module %s\n" filename;
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
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3971);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3977 =
                      let uu____3980 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3980 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3977))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4183 = topological_dependences_of all_cmd_line_files in
      (uu____4183, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4196  ->
    fun f  ->
      match uu____4196 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4217  ->
    fun fn  ->
      match uu____4217 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4236 = FStar_Options.debug_any () in
             if uu____4236
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4243 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4243
            then
              let uu____4246 =
                let uu____4247 =
                  let uu____4248 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4248 in
                digest_of_file1 uu____4247 in
              [uu____4246]
            else [] in
          let binary_deps =
            let uu____4255 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4255
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4265 =
                      (is_interface fn1) &&
                        (let uu____4267 = lowercase_module_name fn1 in
                         uu____4267 = module_name) in
                    Prims.op_Negation uu____4265)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___75_4285 =
            match uu___75_4285 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4305 =
                    let uu____4308 = digest_of_file1 fn2 in uu____4308 :: out in
                  hash_deps uu____4305 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4314  ->
    match uu____4314 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4334 =
                  let uu____4339 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4339 FStar_Option.get in
                match uu____4334 with
                | (f_deps,uu____4361) ->
                    let files =
                      FStar_List.map
                        (file_of_dep file_system_map all_cmd_line_files)
                        f_deps in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files in
                    FStar_Util.print2 "%s: %s\n\n" f
                      (FStar_String.concat " " files1)))
let print_full: deps -> Prims.unit =
  fun uu____4372  ->
    match uu____4372 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        let output_ml_file fst_file =
          let ml_base_name =
            let uu____4388 =
              let uu____4389 =
                let uu____4392 = FStar_Util.basename fst_file in
                check_and_strip_suffix uu____4392 in
              FStar_Option.get uu____4389 in
            FStar_Util.replace_chars uu____4388 46 "_" in
          let dir =
            let uu____4394 = FStar_Options.output_dir () in
            match uu____4394 with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some x -> Prims.strcat x "/" in
          Prims.strcat dir (Prims.strcat ml_base_name ".ml") in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4414 =
                   let uu____4419 = deps_try_find deps f in
                   FStar_All.pipe_right uu____4419 FStar_Option.get in
                 match uu____4414 with
                 | (f_deps,uu____4441) ->
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps in
                     let files1 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files in
                     ((let uu____4451 = is_interface f in
                       if uu____4451
                       then
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" f f
                           (FStar_String.concat "\\\n\t" files1)
                       else ());
                      (let uu____4454 = cache_file_name f in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4454 f
                         (FStar_String.concat " \\\n\t" files1));
                      (let uu____4455 = is_implementation f in
                       if uu____4455
                       then
                         let ml_base_name =
                           let uu____4457 =
                             let uu____4458 =
                               let uu____4461 = FStar_Util.basename f in
                               check_and_strip_suffix uu____4461 in
                             FStar_Option.get uu____4458 in
                           FStar_Util.replace_chars uu____4457 46 "_" in
                         let uu____4462 = output_ml_file f in
                         let uu____4463 = cache_file_name f in
                         FStar_Util.print2 "%s: %s\n\n" uu____4462 uu____4463
                       else ()))));
         (let all_fst_files =
            let uu____4468 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
            FStar_All.pipe_right uu____4468
              (FStar_Util.sort_with FStar_String.compare) in
          let all_ml_files =
            let uu____4482 =
              FStar_All.pipe_right all_fst_files
                (FStar_List.collect
                   (fun fst_file  ->
                      let uu____4493 =
                        let uu____4494 = lowercase_module_name fst_file in
                        FStar_Options.should_extract uu____4494 in
                      if uu____4493
                      then
                        let uu____4497 = output_ml_file fst_file in
                        [uu____4497]
                      else [])) in
            FStar_All.pipe_right uu____4482
              (FStar_Util.sort_with FStar_String.compare) in
          (let uu____4504 =
             FStar_All.pipe_right all_fst_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n" uu____4504);
          (let uu____4507 =
             FStar_All.pipe_right all_ml_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n" uu____4507)))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4513 = FStar_Options.dep () in
    match uu____4513 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4516 = deps in
        (match uu____4516 with
         | Mk (deps1,uu____4518,uu____4519) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4524 ->
        FStar_Errors.raise_err
          (FStar_Errors.UnknowToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()