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
  fun f  -> let uu____141 = is_interface f in Prims.op_Negation uu____141
let list_of_option:
  'Auu____144 .
    'Auu____144 FStar_Pervasives_Native.option -> 'Auu____144 Prims.list
  =
  fun uu___52_152  ->
    match uu___52_152 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____158 .
    ('Auu____158 FStar_Pervasives_Native.option,'Auu____158
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____158 Prims.list
  =
  fun uu____172  ->
    match uu____172 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let module_name_of_file: Prims.string -> Prims.string =
  fun f  ->
    let uu____194 =
      let uu____197 = FStar_Util.basename f in
      check_and_strip_suffix uu____197 in
    match uu____194 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____199 =
          let uu____204 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____204) in
        FStar_Errors.raise_err uu____199
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____208 = module_name_of_file f in FStar_String.lowercase uu____208
let namespace_of_module:
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun f  ->
    let lid =
      FStar_Ident.lid_of_path (FStar_Ident.path_of_text f)
        FStar_Range.dummyRange in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____217 ->
        let uu____220 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
        FStar_Pervasives_Native.Some uu____220
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____237 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____249 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____261 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____272 . Prims.unit -> 'Auu____272 Prims.list =
  fun uu____275  -> []
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
  fun uu____364  ->
    fun k  -> match uu____364 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____393  ->
    fun k  ->
      fun v1  -> match uu____393 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____415  -> match uu____415 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____431  ->
    let uu____432 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____432
let empty_deps: deps =
  let uu____443 =
    let uu____452 = deps_empty () in
    let uu____453 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____452, uu____453, []) in
  Mk uu____443
let module_name_of_dep: dependence -> module_name =
  fun uu___53_486  ->
    match uu___53_486 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____500 = FStar_Util.smap_try_find file_system_map key in
      match uu____500 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____522) ->
          let uu____537 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____537
      | FStar_Pervasives_Native.Some
          (uu____538,FStar_Pervasives_Native.Some fn) ->
          let uu____554 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____554
      | uu____555 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____576 = FStar_Util.smap_try_find file_system_map key in
      match uu____576 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____598) ->
          FStar_Pervasives_Native.Some iface
      | uu____613 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____634 = FStar_Util.smap_try_find file_system_map key in
      match uu____634 with
      | FStar_Pervasives_Native.Some
          (uu____655,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____671 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____688 = interface_of file_system_map key in
      FStar_Option.isSome uu____688
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____697 = implementation_of file_system_map key in
      FStar_Option.isSome uu____697
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let uu____703 =
      let uu____704 = FStar_Options.lax () in
      if uu____704
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked" in
    FStar_Options.prepend_cache_dir uu____703
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
                      (let uu____731 = lowercase_module_name fn in
                       key = uu____731))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____738 = interface_of file_system_map key in
              (match uu____738 with
               | FStar_Pervasives_Native.None  ->
                   let uu____744 =
                     let uu____749 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingInterface, uu____749) in
                   FStar_Errors.raise_err uu____744
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____753 =
                (cmd_line_has_impl key) &&
                  (let uu____755 = FStar_Options.dep () in
                   FStar_Option.isNone uu____755) in
              if uu____753
              then
                let uu____758 = FStar_Options.expose_interfaces () in
                (if uu____758
                 then
                   let uu____759 =
                     let uu____760 = implementation_of file_system_map key in
                     FStar_Option.get uu____760 in
                   maybe_add_suffix uu____759
                 else
                   (let uu____764 =
                      let uu____769 =
                        let uu____770 =
                          let uu____771 =
                            implementation_of file_system_map key in
                          FStar_Option.get uu____771 in
                        let uu____774 =
                          let uu____775 = interface_of file_system_map key in
                          FStar_Option.get uu____775 in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____770 uu____774 in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____769) in
                    FStar_Errors.raise_err uu____764))
              else
                (let uu____779 =
                   let uu____780 = interface_of file_system_map key in
                   FStar_Option.get uu____780 in
                 maybe_add_suffix uu____779)
          | PreferInterface key ->
              let uu____784 = implementation_of file_system_map key in
              (match uu____784 with
               | FStar_Pervasives_Native.None  ->
                   let uu____790 =
                     let uu____795 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____795) in
                   FStar_Errors.raise_err uu____790
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____798 = implementation_of file_system_map key in
              (match uu____798 with
               | FStar_Pervasives_Native.None  ->
                   let uu____804 =
                     let uu____809 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____809) in
                   FStar_Errors.raise_err uu____804
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
          let uu____839 = deps_try_find deps fn in
          match uu____839 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____853) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____884 to_1 =
          match uu____884 with
          | (d,color) ->
              let uu____904 = is_interface to_1 in
              if uu____904
              then
                let uu____911 =
                  let uu____914 =
                    let uu____915 = lowercase_module_name to_1 in
                    PreferInterface uu____915 in
                  uu____914 :: d in
                (uu____911, color)
              else
                (let uu____919 =
                   let uu____922 =
                     let uu____923 = lowercase_module_name to_1 in
                     UseImplementation uu____923 in
                   uu____922 :: d in
                 (uu____919, color)) in
        let uu____926 = deps_try_find deps from in
        match uu____926 with
        | FStar_Pervasives_Native.None  ->
            let uu____937 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____937
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____953 = add_dep key_deps to_ in
            deps_add_dep deps from uu____953
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____964 =
       let uu____965 =
         let uu____966 =
           let uu____967 =
             let uu____970 =
               let uu____973 = deps_keys graph in FStar_List.unique uu____973 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____982 =
                      let uu____987 = deps_try_find graph k in
                      FStar_Util.must uu____987 in
                    FStar_Pervasives_Native.fst uu____982 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____970 in
           FStar_String.concat "\n" uu____967 in
         Prims.strcat uu____966 "\n}\n" in
       Prims.strcat "digraph {\n" uu____965 in
     FStar_Util.write_file "dep.graph" uu____964)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1016  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____1033 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____1033 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1059 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1059
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1080 =
              let uu____1085 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1085) in
            FStar_Errors.raise_err uu____1080)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1125 = FStar_Util.smap_try_find map1 key in
      match uu____1125 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1162 = is_interface full_path in
          if uu____1162
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1196 = is_interface full_path in
          if uu____1196
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1223 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1237  ->
          match uu____1237 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1223);
    FStar_List.iter
      (fun f  ->
         let uu____1248 = lowercase_module_name f in add_entry uu____1248 f)
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
        (let uu____1263 =
           let uu____1266 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1266 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1292 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1292 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1263);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1426 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1426 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1437 = string_of_lid l last1 in
      FStar_String.lowercase uu____1437
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1441 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1441
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1451 =
        let uu____1452 =
          let uu____1453 =
            let uu____1454 =
              let uu____1457 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1457 in
            FStar_Util.must uu____1454 in
          FStar_String.lowercase uu____1453 in
        uu____1452 <> k' in
      if uu____1451
      then
        let uu____1458 =
          let uu____1463 =
            let uu____1464 = string_of_lid lid true in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1464 filename in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1463) in
        FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____1458
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1469 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename in
    let corelibs =
      let uu____1483 = FStar_Options.prims_basename () in
      let uu____1484 =
        let uu____1487 = FStar_Options.pervasives_basename () in
        let uu____1488 =
          let uu____1491 = FStar_Options.pervasives_native_basename () in
          [uu____1491] in
        uu____1487 :: uu____1488 in
      uu____1483 :: uu____1484 in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)] in
       let uu____1526 =
         let uu____1529 = lowercase_module_name full_filename in
         namespace_of_module uu____1529 in
       match uu____1526 with
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
        let uu____1718 =
          let uu____1719 =
            let uu____1720 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1720 in
          Prims.op_Negation uu____1719 in
        if uu____1718
        then
          let uu____1790 =
            let uu____1793 = FStar_ST.op_Bang deps1 in d :: uu____1793 in
          FStar_ST.op_Colon_Equals deps1 uu____1790
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true in
        let uu____1954 = resolve_module_name original_or_working_map key in
        match uu____1954 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____1993 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____1995 = FStar_Options.dep () in
                   uu____1995 = (FStar_Pervasives_Native.Some "full")) in
              if uu____1993
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2034 -> false in
      let record_open_module let_open lid =
        let uu____2044 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid)) in
        if uu____2044
        then true
        else
          (if let_open
           then
             (let uu____2047 =
                let uu____2052 =
                  let uu____2053 = string_of_lid lid true in
                  FStar_Util.format1 "Module not found: %s" uu____2053 in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2052) in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2047)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2061 =
            let uu____2066 =
              let uu____2067 = string_of_lid lid true in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2067 in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2066) in
          FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2061
        else () in
      let record_open let_open lid =
        let uu____2076 = record_open_module let_open lid in
        if uu____2076
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2086 =
        match uu____2086 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2093 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2103 = FStar_Util.smap_try_find original_map alias in
        match uu____2103 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2157 =
                let uu____2162 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2162) in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2157);
             false) in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2167 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2171 = add_dependence_edge working_map module_name in
            if uu____2171
            then ()
            else
              (let uu____2173 = FStar_Options.debug_any () in
               if uu____2173
               then
                 let uu____2174 =
                   let uu____2179 =
                     let uu____2180 = FStar_Ident.string_of_lid module_name in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2180 in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2179) in
                 FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                   uu____2174
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___54_2266 =
         match uu___54_2266 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2275 =
                   let uu____2276 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2276 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2280) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2287 =
                   let uu____2288 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2288 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___55_2297 =
         match uu___55_2297 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2302 = record_module_alias ident lid in
             if uu____2302
             then
               let uu____2303 =
                 let uu____2304 = lowercase_join_longident lid true in
                 PreferInterface uu____2304 in
               add_dep deps uu____2303
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2339,patterms) ->
             FStar_List.iter
               (fun uu____2361  ->
                  match uu____2361 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2370,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2372;
               FStar_Parser_AST.mdest = uu____2373;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2375;
               FStar_Parser_AST.mdest = uu____2376;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2378,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2380;
               FStar_Parser_AST.mdest = uu____2381;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2385,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2415  -> match uu____2415 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2428,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2435 -> ()
         | FStar_Parser_AST.Pragma uu____2436 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2472 =
                 let uu____2473 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2473 > (Prims.parse_int "1") in
               if uu____2472
               then
                 let uu____2515 =
                   let uu____2520 =
                     let uu____2521 = string_of_lid lid true in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2521 in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2520) in
                 FStar_Errors.raise_error uu____2515
                   (FStar_Ident.range_of_lid lid)
               else ()))
       and collect_tycon uu___56_2523 =
         match uu___56_2523 with
         | FStar_Parser_AST.TyconAbstract (uu____2524,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2536,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2550,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2596  ->
                   match uu____2596 with
                   | (uu____2605,t,uu____2607) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2612,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2671  ->
                   match uu____2671 with
                   | (uu____2684,t,uu____2686,uu____2687) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___57_2696 =
         match uu___57_2696 with
         | FStar_Parser_AST.DefineEffect (uu____2697,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2711,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___58_2722 =
         match uu___58_2722 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2723,t);
             FStar_Parser_AST.brange = uu____2725;
             FStar_Parser_AST.blevel = uu____2726;
             FStar_Parser_AST.aqual = uu____2727;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2728,t);
             FStar_Parser_AST.brange = uu____2730;
             FStar_Parser_AST.blevel = uu____2731;
             FStar_Parser_AST.aqual = uu____2732;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2734;
             FStar_Parser_AST.blevel = uu____2735;
             FStar_Parser_AST.aqual = uu____2736;_} -> collect_term t
         | uu____2737 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___59_2739 =
         match uu___59_2739 with
         | FStar_Const.Const_int
             (uu____2740,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____2755 =
               let uu____2756 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____2756 in
             add_dep deps uu____2755
         | FStar_Const.Const_char uu____2790 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____2824 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____2858 -> ()
       and collect_term' uu___60_2859 =
         match uu___60_2859 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____2868 =
                   let uu____2869 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____2869 in
                 collect_term' uu____2868)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____2871 -> ()
         | FStar_Parser_AST.Uvar uu____2872 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____2875) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____2905  ->
                   match uu____2905 with | (t,uu____2911) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____2921) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____2923,patterms,t) ->
             (FStar_List.iter
                (fun uu____2947  ->
                   match uu____2947 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____2958,t1,t2) ->
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
                (fun uu____3054  ->
                   match uu____3054 with | (uu____3059,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3062) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3118,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3121,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3124) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3130) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3136,uu____3137) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___61_3145 =
         match uu___61_3145 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3146 -> ()
         | FStar_Parser_AST.PatConst uu____3147 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3155 -> ()
         | FStar_Parser_AST.PatName uu____3162 -> ()
         | FStar_Parser_AST.PatTvar uu____3163 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3177) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3196  ->
                  match uu____3196 with | (uu____3201,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3225 =
         match uu____3225 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3243 = FStar_Parser_Driver.parse_file filename in
       match uu____3243 with
       | (ast,uu____3263) ->
           let mname = lowercase_module_name filename in
           ((let uu____3278 =
               ((is_interface filename) &&
                  (has_implementation original_map mname))
                 &&
                 (let uu____3280 = FStar_Options.dep () in
                  uu____3280 = (FStar_Pervasives_Native.Some "full")) in
             if uu____3278
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3320 = FStar_ST.op_Bang deps in
             let uu____3368 = FStar_ST.op_Bang mo_roots in
             (uu____3320, uu____3368))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____3450 = FStar_Options.find_file fn in
              match uu____3450 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3453 =
                    let uu____3458 =
                      FStar_Util.format1 "File %s could not be found\n" fn in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3458) in
                  FStar_Errors.raise_err uu____3453
              | FStar_Pervasives_Native.Some fn1 -> fn1)) in
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files1 in
    let rec discover_one file_name =
      let uu____3466 =
        let uu____3467 = deps_try_find dep_graph file_name in
        uu____3467 = FStar_Pervasives_Native.None in
      if uu____3466
      then
        let uu____3484 = collect_one file_system_map file_name in
        match uu____3484 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3507 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3507
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3512 =
                let uu____3517 = FStar_List.unique deps1 in
                (uu____3517, White) in
              deps_add_dep dep_graph file_name uu____3512);
             (let uu____3522 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3522))
      else () in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3555 =
           let uu____3560 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3560 in
         match uu____3555 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  ((let uu____3574 =
                      let uu____3579 =
                        FStar_Util.format1
                          "Recursive dependency on module %s\n" filename in
                      (FStar_Errors.Warning_RecursiveDependency, uu____3579) in
                    FStar_Errors.log_issue FStar_Range.dummyRange uu____3574);
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____3585 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3585);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3591 =
                      let uu____3594 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3594 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3591))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____3740 = topological_dependences_of all_cmd_line_files1 in
      (uu____3740, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____3753  ->
    fun f  ->
      match uu____3753 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option
  =
  fun uu____3778  ->
    fun fn  ->
      match uu____3778 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____3796 = FStar_Options.find_file fn in
            match uu____3796 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____3800 -> fn in
          let cache_file = cache_file_name fn1 in
          let digest_of_file1 fn2 =
            (let uu____3809 = FStar_Options.debug_any () in
             if uu____3809
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2 in
          let module_name = lowercase_module_name fn1 in
          let source_hash = digest_of_file1 fn1 in
          let interface_hash =
            let uu____3820 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name) in
            if uu____3820
            then
              let uu____3827 =
                let uu____3832 =
                  let uu____3833 =
                    let uu____3834 = interface_of file_system_map module_name in
                    FStar_Option.get uu____3834 in
                  digest_of_file1 uu____3833 in
                ("interface", uu____3832) in
              [uu____3827]
            else [] in
          let binary_deps =
            let uu____3853 =
              dependences_of file_system_map deps all_cmd_line_files fn1 in
            FStar_All.pipe_right uu____3853
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____3863 =
                      (is_interface fn2) &&
                        (let uu____3865 = lowercase_module_name fn2 in
                         uu____3865 = module_name) in
                    Prims.op_Negation uu____3863)) in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____3875 = lowercase_module_name fn11 in
                   let uu____3876 = lowercase_module_name fn2 in
                   FStar_String.compare uu____3875 uu____3876) binary_deps in
          let rec hash_deps out uu___62_3899 =
            match uu___62_3899 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name fn2 in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____3943 =
                    let uu____3950 =
                      let uu____3955 = lowercase_module_name fn2 in
                      let uu____3956 = digest_of_file1 cache_fn in
                      (uu____3955, uu____3956) in
                    uu____3950 :: out in
                  hash_deps uu____3943 deps1
                else
                  ((let uu____3963 = FStar_Options.debug_any () in
                    if uu____3963
                    then
                      FStar_Util.print2 "%s: missed digest of file %s\n"
                        cache_file cache_fn
                    else ());
                   FStar_Pervasives_Native.None) in
          hash_deps [] binary_deps1
let print_digest:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string
  =
  fun dig  ->
    let uu____3990 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4009  ->
              match uu____4009 with
              | (m,d) ->
                  let uu____4016 = FStar_Util.base64_encode d in
                  FStar_Util.format2 "%s:%s" m uu____4016)) in
    FStar_All.pipe_right uu____3990 (FStar_String.concat "\n")
let print_make: deps -> Prims.unit =
  fun uu____4021  ->
    match uu____4021 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4041 =
                  let uu____4046 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4046 FStar_Option.get in
                match uu____4041 with
                | (f_deps,uu____4068) ->
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
  fun uu____4080  ->
    match uu____4080 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref [] in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41") in
          let should_visit lc_module_name =
            (let uu____4117 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name in
             FStar_Option.isSome uu____4117) ||
              (let uu____4121 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name in
               FStar_Option.isNone uu____4121) in
          let mark_visiting lc_module_name =
            let ml_file_opt =
              FStar_Util.smap_try_find remaining_output_files lc_module_name in
            FStar_Util.smap_remove remaining_output_files lc_module_name;
            FStar_Util.smap_add visited_other_modules lc_module_name true;
            ml_file_opt in
          let emit_output_file_opt ml_file_opt =
            match ml_file_opt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some ml_file ->
                let uu____4144 =
                  let uu____4147 = FStar_ST.op_Bang order in ml_file ::
                    uu____4147 in
                FStar_ST.op_Colon_Equals order uu____4144 in
          let rec aux uu___63_4245 =
            match uu___63_4245 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____4261 = deps_try_find deps file_name in
                      (match uu____4261 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____4272 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name in
                           failwith uu____4272
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____4274) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps in
                           aux immediate_deps1) in
                ((let uu____4285 = should_visit lc_module_name in
                  if uu____4285
                  then
                    let ml_file_opt = mark_visiting lc_module_name in
                    ((let uu____4290 =
                        implementation_of file_system_map lc_module_name in
                      visit_file uu____4290);
                     (let uu____4294 =
                        interface_of file_system_map lc_module_name in
                      visit_file uu____4294);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract) in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map in
          aux all_extracted_modules;
          (let uu____4302 = FStar_ST.op_Bang order in
           FStar_List.rev uu____4302) in
        let keys = deps_keys deps in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____4361 =
              let uu____4362 =
                let uu____4365 = FStar_Util.basename fst_file in
                check_and_strip_suffix uu____4365 in
              FStar_Option.get uu____4362 in
            FStar_Util.replace_chars uu____4361 46 "_" in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext) in
        let norm_path s = FStar_Util.replace_chars s 92 "/" in
        let output_ml_file f =
          let uu____4376 = output_file ".ml" f in norm_path uu____4376 in
        let output_krml_file f =
          let uu____4381 = output_file ".krml" f in norm_path uu____4381 in
        let output_cmx_file f =
          let uu____4386 = output_file ".cmx" f in norm_path uu____4386 in
        let cache_file f =
          let uu____4391 = cache_file_name f in norm_path uu____4391 in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4413 =
                   let uu____4418 = deps_try_find deps f in
                   FStar_All.pipe_right uu____4418 FStar_Option.get in
                 match uu____4413 with
                 | (f_deps,uu____4440) ->
                     let norm_f = norm_path f in
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps in
                     let files1 = FStar_List.map norm_path files in
                     let files2 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files1 in
                     let files3 = FStar_String.concat "\\\n\t" files2 in
                     ((let uu____4456 = is_interface f in
                       if uu____4456
                       then
                         let uu____4457 =
                           let uu____4458 =
                             FStar_Options.prepend_cache_dir norm_f in
                           norm_path uu____4458 in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____4457 norm_f files3
                       else ());
                      (let uu____4461 = cache_file f in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4461
                         norm_f files3);
                      (let uu____4462 = is_implementation f in
                       if uu____4462
                       then
                         ((let uu____4464 = output_ml_file f in
                           let uu____4465 = cache_file f in
                           FStar_Util.print2 "%s: %s\n\n" uu____4464
                             uu____4465);
                          (let cmx_files =
                             let fst_files =
                               FStar_All.pipe_right f_deps
                                 (FStar_List.map
                                    (file_of_dep_aux false file_system_map
                                       all_cmd_line_files)) in
                             let extracted_fst_files =
                               FStar_All.pipe_right fst_files
                                 (FStar_List.filter
                                    (fun df  ->
                                       (let uu____4487 =
                                          lowercase_module_name df in
                                        let uu____4488 =
                                          lowercase_module_name f in
                                        uu____4487 <> uu____4488) &&
                                         (let uu____4490 =
                                            lowercase_module_name df in
                                          FStar_Options.should_extract
                                            uu____4490))) in
                             FStar_All.pipe_right extracted_fst_files
                               (FStar_List.map output_cmx_file) in
                           (let uu____4496 =
                              let uu____4497 = lowercase_module_name f in
                              FStar_Options.should_extract uu____4497 in
                            if uu____4496
                            then
                              let uu____4498 = output_cmx_file f in
                              let uu____4499 = output_ml_file f in
                              FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                uu____4498 uu____4499
                                (FStar_String.concat "\\\n\t" cmx_files)
                            else ());
                           (let uu____4501 = output_krml_file f in
                            let uu____4502 = cache_file f in
                            FStar_Util.print2 "%s: %s\n\n" uu____4501
                              uu____4502)))
                       else
                         (let uu____4504 =
                            (let uu____4507 =
                               let uu____4508 = lowercase_module_name f in
                               has_implementation file_system_map uu____4508 in
                             Prims.op_Negation uu____4507) &&
                              (is_interface f) in
                          if uu____4504
                          then
                            let uu____4509 = output_krml_file f in
                            let uu____4510 = cache_file f in
                            FStar_Util.print2 "%s: %s\n\n" uu____4509
                              uu____4510
                          else ())))));
         (let all_fst_files =
            let uu____4515 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
            FStar_All.pipe_right uu____4515
              (FStar_Util.sort_with FStar_String.compare) in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41") in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file in
                    let uu____4541 = FStar_Options.should_extract mname in
                    if uu____4541
                    then
                      let uu____4542 = output_ml_file fst_file in
                      FStar_Util.smap_add ml_file_map mname uu____4542
                    else ()));
            sort_output_files ml_file_map in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41") in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file in
                    let uu____4558 = output_krml_file fst_file in
                    FStar_Util.smap_add krml_file_map mname uu____4558));
            sort_output_files krml_file_map in
          (let uu____4560 =
             let uu____4561 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path) in
             FStar_All.pipe_right uu____4561 (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____4560);
          (let uu____4571 =
             let uu____4572 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path) in
             FStar_All.pipe_right uu____4572 (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____4571);
          (let uu____4581 =
             let uu____4582 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path) in
             FStar_All.pipe_right uu____4582 (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____4581)))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4594 = FStar_Options.dep () in
    match uu____4594 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4597 = deps in
        (match uu____4597 with
         | Mk (deps1,uu____4599,uu____4600) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4605 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()