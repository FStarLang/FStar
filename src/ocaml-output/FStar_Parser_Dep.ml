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
  fun uu___50_152  ->
    match uu___50_152 with
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
  fun uu___51_486  ->
    match uu___51_486 with
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
    let uu____703 = FStar_Options.lax () in
    if uu____703
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
                      (let uu____730 = lowercase_module_name fn in
                       key = uu____730))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____737 = interface_of file_system_map key in
              (match uu____737 with
               | FStar_Pervasives_Native.None  ->
                   let uu____743 =
                     let uu____748 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingInterface, uu____748) in
                   FStar_Errors.raise_err uu____743
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file then Prims.strcat f ".source" else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____752 =
                (cmd_line_has_impl key) &&
                  (let uu____754 = FStar_Options.dep () in
                   FStar_Option.isNone uu____754) in
              if uu____752
              then
                let uu____757 = FStar_Options.expose_interfaces () in
                (if uu____757
                 then
                   let uu____758 =
                     let uu____759 = implementation_of file_system_map key in
                     FStar_Option.get uu____759 in
                   maybe_add_suffix uu____758
                 else
                   (let uu____763 =
                      let uu____768 =
                        let uu____769 =
                          let uu____770 =
                            implementation_of file_system_map key in
                          FStar_Option.get uu____770 in
                        let uu____773 =
                          let uu____774 = interface_of file_system_map key in
                          FStar_Option.get uu____774 in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____769 uu____773 in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____768) in
                    FStar_Errors.raise_err uu____763))
              else
                (let uu____778 =
                   let uu____779 = interface_of file_system_map key in
                   FStar_Option.get uu____779 in
                 maybe_add_suffix uu____778)
          | PreferInterface key ->
              let uu____783 = implementation_of file_system_map key in
              (match uu____783 with
               | FStar_Pervasives_Native.None  ->
                   let uu____789 =
                     let uu____794 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____794) in
                   FStar_Errors.raise_err uu____789
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____797 = implementation_of file_system_map key in
              (match uu____797 with
               | FStar_Pervasives_Native.None  ->
                   let uu____803 =
                     let uu____808 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     (FStar_Errors.Fatal_MissingImplementation, uu____808) in
                   FStar_Errors.raise_err uu____803
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
          let uu____838 = deps_try_find deps fn in
          match uu____838 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____852) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____883 to_1 =
          match uu____883 with
          | (d,color) ->
              let uu____903 = is_interface to_1 in
              if uu____903
              then
                let uu____910 =
                  let uu____913 =
                    let uu____914 = lowercase_module_name to_1 in
                    PreferInterface uu____914 in
                  uu____913 :: d in
                (uu____910, color)
              else
                (let uu____918 =
                   let uu____921 =
                     let uu____922 = lowercase_module_name to_1 in
                     UseImplementation uu____922 in
                   uu____921 :: d in
                 (uu____918, color)) in
        let uu____925 = deps_try_find deps from in
        match uu____925 with
        | FStar_Pervasives_Native.None  ->
            let uu____936 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____936
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____952 = add_dep key_deps to_ in
            deps_add_dep deps from uu____952
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____963 =
       let uu____964 =
         let uu____965 =
           let uu____966 =
             let uu____969 =
               let uu____972 = deps_keys graph in FStar_List.unique uu____972 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____981 =
                      let uu____986 = deps_try_find graph k in
                      FStar_Util.must uu____986 in
                    FStar_Pervasives_Native.fst uu____981 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____969 in
           FStar_String.concat "\n" uu____966 in
         Prims.strcat uu____965 "\n}\n" in
       Prims.strcat "digraph {\n" uu____964 in
     FStar_Util.write_file "dep.graph" uu____963)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1015  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____1032 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____1032 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1058 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1058
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1079 =
              let uu____1084 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1084) in
            FStar_Errors.raise_err uu____1079)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1124 = FStar_Util.smap_try_find map1 key in
      match uu____1124 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1161 = is_interface full_path in
          if uu____1161
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1195 = is_interface full_path in
          if uu____1195
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1222 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1236  ->
          match uu____1236 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1222);
    FStar_List.iter
      (fun f  ->
         let uu____1247 = lowercase_module_name f in add_entry uu____1247 f)
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
        (let uu____1262 =
           let uu____1265 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1265 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1291 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1291 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1262);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1483 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1483 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1494 = string_of_lid l last1 in
      FStar_String.lowercase uu____1494
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1498 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1498
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1508 =
        let uu____1509 =
          let uu____1510 =
            let uu____1511 =
              let uu____1514 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1514 in
            FStar_Util.must uu____1511 in
          FStar_String.lowercase uu____1510 in
        uu____1509 <> k' in
      if uu____1508
      then
        let uu____1515 =
          let uu____1520 =
            let uu____1521 = string_of_lid lid true in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1521 filename in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1520) in
        FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____1515
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1526 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename in
    let corelibs =
      let uu____1540 = FStar_Options.prims_basename () in
      let uu____1541 =
        let uu____1544 = FStar_Options.pervasives_basename () in
        let uu____1545 =
          let uu____1548 = FStar_Options.pervasives_native_basename () in
          [uu____1548] in
        uu____1544 :: uu____1545 in
      uu____1540 :: uu____1541 in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)] in
       let uu____1583 =
         let uu____1586 = lowercase_module_name full_filename in
         namespace_of_module uu____1586 in
       match uu____1583 with
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
        let uu____1999 =
          let uu____2000 =
            let uu____2001 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____2001 in
          Prims.op_Negation uu____2000 in
        if uu____1999
        then
          let uu____2158 =
            let uu____2161 = FStar_ST.op_Bang deps1 in d :: uu____2161 in
          FStar_ST.op_Colon_Equals deps1 uu____2158
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true in
        let uu____2496 = resolve_module_name original_or_working_map key in
        match uu____2496 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2535 =
                ((has_interface original_or_working_map module_name) &&
                   (has_implementation original_or_working_map module_name))
                  &&
                  (let uu____2537 = FStar_Options.dep () in
                   uu____2537 = (FStar_Pervasives_Native.Some "full")) in
              if uu____2535
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2576 -> false in
      let record_open_module let_open lid =
        let uu____2586 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid)) in
        if uu____2586
        then true
        else
          (if let_open
           then
             (let uu____2589 =
                let uu____2594 =
                  let uu____2595 = string_of_lid lid true in
                  FStar_Util.format1 "Module not found: %s" uu____2595 in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2594) in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2589)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2603 =
            let uu____2608 =
              let uu____2609 = string_of_lid lid true in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2609 in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2608) in
          FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2603
        else () in
      let record_open let_open lid =
        let uu____2618 = record_open_module let_open lid in
        if uu____2618
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2628 =
        match uu____2628 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2635 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2645 = FStar_Util.smap_try_find original_map alias in
        match uu____2645 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2699 =
                let uu____2704 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2704) in
              FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                uu____2699);
             false) in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2709 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2713 = add_dependence_edge working_map module_name in
            if uu____2713
            then ()
            else
              (let uu____2715 = FStar_Options.debug_any () in
               if uu____2715
               then
                 let uu____2716 =
                   let uu____2721 =
                     let uu____2722 = FStar_Ident.string_of_lid module_name in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2722 in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2721) in
                 FStar_Errors.log_issue (FStar_Ident.range_of_lid lid)
                   uu____2716
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___52_2808 =
         match uu___52_2808 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2817 =
                   let uu____2818 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2818 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2822) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2829 =
                   let uu____2830 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2830 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___53_2839 =
         match uu___53_2839 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2844 = record_module_alias ident lid in
             if uu____2844
             then
               let uu____2845 =
                 let uu____2846 = lowercase_join_longident lid true in
                 PreferInterface uu____2846 in
               add_dep deps uu____2845
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2881,patterms) ->
             FStar_List.iter
               (fun uu____2903  ->
                  match uu____2903 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2912,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2914;
               FStar_Parser_AST.mdest = uu____2915;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2917;
               FStar_Parser_AST.mdest = uu____2918;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2920,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2922;
               FStar_Parser_AST.mdest = uu____2923;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2927,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2957  -> match uu____2957 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2970,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2977 -> ()
         | FStar_Parser_AST.Pragma uu____2978 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____3014 =
                 let uu____3015 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____3015 > (Prims.parse_int "1") in
               if uu____3014
               then
                 let uu____3086 =
                   let uu____3091 =
                     let uu____3092 = string_of_lid lid true in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____3092 in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____3091) in
                 FStar_Errors.raise_error uu____3086
                   (FStar_Ident.range_of_lid lid)
               else ()))
       and collect_tycon uu___54_3094 =
         match uu___54_3094 with
         | FStar_Parser_AST.TyconAbstract (uu____3095,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____3107,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____3121,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3167  ->
                   match uu____3167 with
                   | (uu____3176,t,uu____3178) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3183,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3242  ->
                   match uu____3242 with
                   | (uu____3255,t,uu____3257,uu____3258) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___55_3267 =
         match uu___55_3267 with
         | FStar_Parser_AST.DefineEffect (uu____3268,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3282,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___56_3293 =
         match uu___56_3293 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3294,t);
             FStar_Parser_AST.brange = uu____3296;
             FStar_Parser_AST.blevel = uu____3297;
             FStar_Parser_AST.aqual = uu____3298;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3299,t);
             FStar_Parser_AST.brange = uu____3301;
             FStar_Parser_AST.blevel = uu____3302;
             FStar_Parser_AST.aqual = uu____3303;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3305;
             FStar_Parser_AST.blevel = uu____3306;
             FStar_Parser_AST.aqual = uu____3307;_} -> collect_term t
         | uu____3308 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___57_3310 =
         match uu___57_3310 with
         | FStar_Const.Const_int
             (uu____3311,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3326 =
               let uu____3327 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3327 in
             add_dep deps uu____3326
         | FStar_Const.Const_char uu____3361 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3395 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3429 -> ()
       and collect_term' uu___58_3430 =
         match uu___58_3430 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3439 =
                   let uu____3440 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3440 in
                 collect_term' uu____3439)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3442 -> ()
         | FStar_Parser_AST.Uvar uu____3443 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3446) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3476  ->
                   match uu____3476 with | (t,uu____3482) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3492) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3494,patterms,t) ->
             (FStar_List.iter
                (fun uu____3518  ->
                   match uu____3518 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3529,t1,t2) ->
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
                (fun uu____3625  ->
                   match uu____3625 with | (uu____3630,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3633) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3689,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3692,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3695) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3701) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3707,uu____3708) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___59_3716 =
         match uu___59_3716 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3717 -> ()
         | FStar_Parser_AST.PatConst uu____3718 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3726 -> ()
         | FStar_Parser_AST.PatName uu____3733 -> ()
         | FStar_Parser_AST.PatTvar uu____3734 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3748) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3767  ->
                  match uu____3767 with | (uu____3772,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3796 =
         match uu____3796 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3814 = FStar_Parser_Driver.parse_file filename in
       match uu____3814 with
       | (ast,uu____3834) ->
           (collect_module ast;
            (let uu____3848 = FStar_ST.op_Bang deps in
             let uu____3925 = FStar_ST.op_Bang mo_roots in
             (uu____3848, uu____3925))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____4031 =
        let uu____4032 = deps_try_find dep_graph file_name in
        uu____4032 = FStar_Pervasives_Native.None in
      if uu____4031
      then
        let uu____4049 = collect_one file_system_map file_name in
        match uu____4049 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____4072 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____4072
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____4077 =
                let uu____4082 = FStar_List.unique deps1 in
                (uu____4082, White) in
              deps_add_dep dep_graph file_name uu____4077);
             (let uu____4087 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____4087))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____4120 =
           let uu____4125 = deps_try_find dep_graph filename in
           FStar_Util.must uu____4125 in
         match uu____4120 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  ((let uu____4139 =
                      let uu____4144 =
                        FStar_Util.format1
                          "Recursive dependency on module %s\n" filename in
                      (FStar_Errors.Warning_RecursiveDependency, uu____4144) in
                    FStar_Errors.log_issue FStar_Range.dummyRange uu____4139);
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____4150 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4150);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____4156 =
                      let uu____4159 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____4159 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____4156))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4392 = topological_dependences_of all_cmd_line_files in
      (uu____4392, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4405  ->
    fun f  ->
      match uu____4405 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option
  =
  fun uu____4430  ->
    fun fn  ->
      match uu____4430 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4453 = FStar_Options.debug_any () in
             if uu____4453
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4464 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4464
            then
              let uu____4471 =
                let uu____4476 =
                  let uu____4477 =
                    let uu____4478 = interface_of file_system_map module_name in
                    FStar_Option.get uu____4478 in
                  digest_of_file1 uu____4477 in
                ("interface", uu____4476) in
              [uu____4471]
            else [] in
          let binary_deps =
            let uu____4497 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4497
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4507 =
                      (is_interface fn1) &&
                        (let uu____4509 = lowercase_module_name fn1 in
                         uu____4509 = module_name) in
                    Prims.op_Negation uu____4507)) in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn1  ->
                 fun fn2  ->
                   let uu____4519 = lowercase_module_name fn1 in
                   let uu____4520 = lowercase_module_name fn2 in
                   FStar_String.compare uu____4519 uu____4520) binary_deps in
          let rec hash_deps out uu___60_4543 =
            match uu___60_4543 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn1::deps1 ->
                let cache_fn = cache_file_name fn1 in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4587 =
                    let uu____4594 =
                      let uu____4599 = lowercase_module_name fn1 in
                      let uu____4600 = digest_of_file1 cache_fn in
                      (uu____4599, uu____4600) in
                    uu____4594 :: out in
                  hash_deps uu____4587 deps1
                else
                  ((let uu____4607 = FStar_Options.debug_any () in
                    if uu____4607
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
    let uu____4634 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4653  ->
              match uu____4653 with
              | (m,d) ->
                  let uu____4660 = FStar_Util.base64_encode d in
                  FStar_Util.format2 "%s:%s" m uu____4660)) in
    FStar_All.pipe_right uu____4634 (FStar_String.concat "\n")
let print_make: deps -> Prims.unit =
  fun uu____4665  ->
    match uu____4665 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4685 =
                  let uu____4690 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4690 FStar_Option.get in
                match uu____4685 with
                | (f_deps,uu____4712) ->
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
  fun uu____4724  ->
    match uu____4724 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____4743 =
              let uu____4744 =
                let uu____4747 = FStar_Util.basename fst_file in
                check_and_strip_suffix uu____4747 in
              FStar_Option.get uu____4744 in
            FStar_Util.replace_chars uu____4743 46 "_" in
          let dir =
            let uu____4750 = FStar_Options.output_dir () in
            match uu____4750 with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some x -> Prims.strcat x "/" in
          Prims.strcat dir (Prims.strcat ml_base_name ext) in
        let output_ml_file = output_file ".ml" in
        let output_krml_file = output_file ".krml" in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4776 =
                   let uu____4781 = deps_try_find deps f in
                   FStar_All.pipe_right uu____4781 FStar_Option.get in
                 match uu____4776 with
                 | (f_deps,uu____4803) ->
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps in
                     let files1 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files in
                     ((let uu____4814 = is_interface f in
                       if uu____4814
                       then
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" f f
                           (FStar_String.concat "\\\n\t" files1)
                       else ());
                      (let uu____4817 = cache_file_name f in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4817 f
                         (FStar_String.concat " \\\n\t" files1));
                      (let uu____4818 = is_implementation f in
                       if uu____4818
                       then
                         ((let uu____4820 = output_ml_file f in
                           let uu____4821 = cache_file_name f in
                           FStar_Util.print2 "%s: %s\n\n" uu____4820
                             uu____4821);
                          (let uu____4822 = output_krml_file f in
                           let uu____4823 = cache_file_name f in
                           FStar_Util.print2 "%s: %s\n\n" uu____4822
                             uu____4823))
                       else
                         (let uu____4825 =
                            (let uu____4828 =
                               let uu____4829 = lowercase_module_name f in
                               has_implementation file_system_map uu____4829 in
                             Prims.op_Negation uu____4828) &&
                              (is_interface f) in
                          if uu____4825
                          then
                            let uu____4830 = output_krml_file f in
                            let uu____4831 = cache_file_name f in
                            FStar_Util.print2 "%s: %s\n\n" uu____4830
                              uu____4831
                          else ())))));
         (let all_fst_files =
            let uu____4836 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
            FStar_All.pipe_right uu____4836
              (FStar_Util.sort_with FStar_String.compare) in
          let all_ml_files =
            let uu____4850 =
              FStar_All.pipe_right all_fst_files
                (FStar_List.collect
                   (fun fst_file  ->
                      let uu____4861 =
                        let uu____4862 = lowercase_module_name fst_file in
                        FStar_Options.should_extract uu____4862 in
                      if uu____4861
                      then
                        let uu____4865 = output_ml_file fst_file in
                        [uu____4865]
                      else [])) in
            FStar_All.pipe_right uu____4850
              (FStar_Util.sort_with FStar_String.compare) in
          let all_krml_files = FStar_List.map output_krml_file keys in
          (let uu____4875 =
             FStar_All.pipe_right all_fst_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n" uu____4875);
          (let uu____4879 =
             FStar_All.pipe_right all_ml_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n" uu____4879);
          (let uu____4882 =
             FStar_All.pipe_right all_krml_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____4882)))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4888 = FStar_Options.dep () in
    match uu____4888 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4891 = deps in
        (match uu____4891 with
         | Mk (deps1,uu____4893,uu____4894) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4899 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()