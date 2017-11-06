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
  fun uu___112_149  ->
    match uu___112_149 with
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
          let uu____197 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____197 in
        FStar_Exn.raise uu____196
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____201 = module_name_of_file f in FStar_String.lowercase uu____201
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____218 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____230 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____242 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____253 . Prims.unit -> 'Auu____253 Prims.list =
  fun uu____256  -> []
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
  fun uu____345  ->
    fun k  -> match uu____345 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____374  ->
    fun k  ->
      fun v1  -> match uu____374 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____396  -> match uu____396 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____412  ->
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____413
let empty_deps: deps =
  let uu____424 =
    let uu____433 = deps_empty () in
    let uu____434 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____433, uu____434, []) in
  Mk uu____424
let module_name_of_dep: dependence -> module_name =
  fun uu___113_467  ->
    match uu___113_467 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____481 = FStar_Util.smap_try_find file_system_map key in
      match uu____481 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____503) ->
          let uu____518 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____518
      | FStar_Pervasives_Native.Some
          (uu____519,FStar_Pervasives_Native.Some fn) ->
          let uu____535 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____535
      | uu____536 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____557 = FStar_Util.smap_try_find file_system_map key in
      match uu____557 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____579) ->
          FStar_Pervasives_Native.Some iface
      | uu____594 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____615 = FStar_Util.smap_try_find file_system_map key in
      match uu____615 with
      | FStar_Pervasives_Native.Some
          (uu____636,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____652 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____669 = interface_of file_system_map key in
      FStar_Option.isSome uu____669
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____678 = implementation_of file_system_map key in
      FStar_Option.isSome uu____678
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let uu____684 = FStar_Options.lax () in
    if uu____684
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
                      (let uu____711 = lowercase_module_name fn in
                       key = uu____711))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____718 = interface_of file_system_map key in
              (match uu____718 with
               | FStar_Pervasives_Native.None  ->
                   let uu____724 =
                     let uu____725 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____725 in
                   FStar_Exn.raise uu____724
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file then Prims.strcat f ".source" else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____729 =
                (cmd_line_has_impl key) &&
                  (let uu____731 = FStar_Options.dep () in
                   FStar_Option.isNone uu____731) in
              if uu____729
              then
                let uu____734 = FStar_Options.expose_interfaces () in
                (if uu____734
                 then
                   let uu____735 =
                     let uu____736 = implementation_of file_system_map key in
                     FStar_Option.get uu____736 in
                   maybe_add_suffix uu____735
                 else
                   (let uu____740 =
                      let uu____741 =
                        let uu____742 =
                          let uu____743 =
                            implementation_of file_system_map key in
                          FStar_Option.get uu____743 in
                        let uu____746 =
                          let uu____747 = interface_of file_system_map key in
                          FStar_Option.get uu____747 in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____742 uu____746 in
                      FStar_Errors.Err uu____741 in
                    FStar_Exn.raise uu____740))
              else
                (let uu____751 =
                   let uu____752 = interface_of file_system_map key in
                   FStar_Option.get uu____752 in
                 maybe_add_suffix uu____751)
          | PreferInterface key ->
              let uu____756 = implementation_of file_system_map key in
              (match uu____756 with
               | FStar_Pervasives_Native.None  ->
                   let uu____762 =
                     let uu____763 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____763 in
                   FStar_Exn.raise uu____762
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____766 = implementation_of file_system_map key in
              (match uu____766 with
               | FStar_Pervasives_Native.None  ->
                   let uu____772 =
                     let uu____773 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____773 in
                   FStar_Exn.raise uu____772
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
          let uu____803 = deps_try_find deps fn in
          match uu____803 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____817) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____848 to_1 =
          match uu____848 with
          | (d,color) ->
              let uu____868 = is_interface to_1 in
              if uu____868
              then
                let uu____875 =
                  let uu____878 =
                    let uu____879 = lowercase_module_name to_1 in
                    PreferInterface uu____879 in
                  uu____878 :: d in
                (uu____875, color)
              else
                (let uu____883 =
                   let uu____886 =
                     let uu____887 = lowercase_module_name to_1 in
                     UseImplementation uu____887 in
                   uu____886 :: d in
                 (uu____883, color)) in
        let uu____890 = deps_try_find deps from in
        match uu____890 with
        | FStar_Pervasives_Native.None  ->
            let uu____901 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____901
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____917 = add_dep key_deps to_ in
            deps_add_dep deps from uu____917
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____928 =
       let uu____929 =
         let uu____930 =
           let uu____931 =
             let uu____934 =
               let uu____937 = deps_keys graph in FStar_List.unique uu____937 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____946 =
                      let uu____951 = deps_try_find graph k in
                      FStar_Util.must uu____951 in
                    FStar_Pervasives_Native.fst uu____946 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____934 in
           FStar_String.concat "\n" uu____931 in
         Prims.strcat uu____930 "\n}\n" in
       Prims.strcat "digraph {\n" uu____929 in
     FStar_Util.write_file "dep.graph" uu____928)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____978  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____995 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____995 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1021 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1021
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1042 =
              let uu____1043 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____1043 in
            FStar_Exn.raise uu____1042)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1083 = FStar_Util.smap_try_find map1 key in
      match uu____1083 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1120 = is_interface full_path in
          if uu____1120
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1154 = is_interface full_path in
          if uu____1154
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1181 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1195  ->
          match uu____1195 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1181);
    FStar_List.iter
      (fun f  ->
         let uu____1206 = lowercase_module_name f in add_entry uu____1206 f)
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
        (let uu____1221 =
           let uu____1224 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1224 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1250 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1250 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1221);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1422 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1422 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1433 = string_of_lid l last1 in
      FStar_String.lowercase uu____1433
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1437 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1437
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1447 =
        let uu____1448 =
          let uu____1449 =
            let uu____1450 =
              let uu____1453 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1453 in
            FStar_Util.must uu____1450 in
          FStar_String.lowercase uu____1449 in
        uu____1448 <> k' in
      if uu____1447
      then
        let uu____1454 =
          let uu____1455 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1455 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1454
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1460 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1474 = FStar_Options.prims_basename () in
      let uu____1475 =
        let uu____1478 = FStar_Options.pervasives_basename () in
        let uu____1479 =
          let uu____1482 = FStar_Options.pervasives_native_basename () in
          [uu____1482] in
        uu____1478 :: uu____1479 in
      uu____1474 :: uu____1475 in
    if FStar_List.mem filename1 corelibs
    then []
    else
      [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
      (FStar_Parser_Const.prims_lid, Open_module);
      (FStar_Parser_Const.pervasives_lid, Open_module)]
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
        let uu____1893 =
          let uu____1894 =
            let uu____1895 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1895 in
          Prims.op_Negation uu____1894 in
        if uu____1893
        then
          let uu____2046 =
            let uu____2049 = FStar_ST.op_Bang deps1 in d :: uu____2049 in
          FStar_ST.op_Colon_Equals deps1 uu____2046
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge lid =
        let key = lowercase_join_longident lid true in
        let uu____2369 = resolve_module_name working_map key in
        match uu____2369 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2396 =
                (has_interface working_map module_name) &&
                  (has_implementation working_map module_name) in
              if uu____2396
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2419 -> false in
      let record_open_module let_open lid =
        let uu____2429 = add_dependence_edge lid in
        if uu____2429
        then true
        else
          (if let_open
           then
             (let uu____2432 =
                let uu____2433 = string_of_lid lid true in
                FStar_Util.format1 "Module not found: %s" uu____2433 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2432)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2441 =
            let uu____2442 = string_of_lid lid true in
            FStar_Util.format1
              "No modules in namespace %s and no file with that name either"
              uu____2442 in
          FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2441
        else () in
      let record_open let_open lid =
        let uu____2451 = record_open_module let_open lid in
        if uu____2451
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2461 =
        match uu____2461 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2468 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2478 = FStar_Util.smap_try_find original_map alias in
        match uu____2478 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2530 =
              FStar_Util.format1 "module not found in search path: %s\n"
                alias in
            FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2530 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2535 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2539 = add_dependence_edge module_name in
            if uu____2539
            then ()
            else
              (let uu____2541 = FStar_Options.debug_any () in
               if uu____2541
               then
                 let uu____2542 =
                   let uu____2543 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2543 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2542
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___114_2629 =
         match uu___114_2629 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2638 =
                   let uu____2639 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2639 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2643) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2650 =
                   let uu____2651 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2651 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___115_2660 =
         match uu___115_2660 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2666 =
                 let uu____2667 = lowercase_join_longident lid true in
                 PreferInterface uu____2667 in
               add_dep deps uu____2666);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2689,patterms) ->
             FStar_List.iter
               (fun uu____2711  ->
                  match uu____2711 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2720,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2722;
               FStar_Parser_AST.mdest = uu____2723;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2725;
               FStar_Parser_AST.mdest = uu____2726;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2728,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2730;
               FStar_Parser_AST.mdest = uu____2731;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2735,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2765  -> match uu____2765 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2778,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2785 -> ()
         | FStar_Parser_AST.Pragma uu____2786 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2810 =
                 let uu____2811 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2811 > (Prims.parse_int "1") in
               if uu____2810
               then
                 let uu____2872 =
                   let uu____2873 =
                     let uu____2878 =
                       let uu____2879 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2879 in
                     (uu____2878, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2873 in
                 FStar_Exn.raise uu____2872
               else ()))
       and collect_tycon uu___116_2881 =
         match uu___116_2881 with
         | FStar_Parser_AST.TyconAbstract (uu____2882,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2894,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2908,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2954  ->
                   match uu____2954 with
                   | (uu____2963,t,uu____2965) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2970,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3029  ->
                   match uu____3029 with
                   | (uu____3042,t,uu____3044,uu____3045) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___117_3054 =
         match uu___117_3054 with
         | FStar_Parser_AST.DefineEffect (uu____3055,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3069,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___118_3080 =
         match uu___118_3080 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3081,t);
             FStar_Parser_AST.brange = uu____3083;
             FStar_Parser_AST.blevel = uu____3084;
             FStar_Parser_AST.aqual = uu____3085;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3086,t);
             FStar_Parser_AST.brange = uu____3088;
             FStar_Parser_AST.blevel = uu____3089;
             FStar_Parser_AST.aqual = uu____3090;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3092;
             FStar_Parser_AST.blevel = uu____3093;
             FStar_Parser_AST.aqual = uu____3094;_} -> collect_term t
         | uu____3095 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___119_3097 =
         match uu___119_3097 with
         | FStar_Const.Const_int
             (uu____3098,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3113 =
               let uu____3114 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3114 in
             add_dep deps uu____3113
         | FStar_Const.Const_char uu____3136 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3158 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3180 -> ()
       and collect_term' uu___120_3181 =
         match uu___120_3181 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3190 =
                   let uu____3191 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3191 in
                 collect_term' uu____3190)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3193 -> ()
         | FStar_Parser_AST.Uvar uu____3194 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3197) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3227  ->
                   match uu____3227 with | (t,uu____3233) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3243) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3245,patterms,t) ->
             (FStar_List.iter
                (fun uu____3269  ->
                   match uu____3269 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3280,t1,t2) ->
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
                (fun uu____3376  ->
                   match uu____3376 with | (uu____3381,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3384) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3440,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3443,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3446) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3452) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3458,uu____3459) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___121_3467 =
         match uu___121_3467 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3468 -> ()
         | FStar_Parser_AST.PatConst uu____3469 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3477 -> ()
         | FStar_Parser_AST.PatName uu____3484 -> ()
         | FStar_Parser_AST.PatTvar uu____3485 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3499) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3518  ->
                  match uu____3518 with | (uu____3523,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3547 =
         match uu____3547 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3565 = FStar_Parser_Driver.parse_file filename in
       match uu____3565 with
       | (ast,uu____3585) ->
           (collect_module ast;
            (let uu____3599 = FStar_ST.op_Bang deps in
             let uu____3666 = FStar_ST.op_Bang mo_roots in
             (uu____3599, uu____3666))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3762 =
        let uu____3763 = deps_try_find dep_graph file_name in
        uu____3763 = FStar_Pervasives_Native.None in
      if uu____3762
      then
        let uu____3780 = collect_one file_system_map file_name in
        match uu____3780 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3803 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3803
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3808 =
                let uu____3813 = FStar_List.unique deps1 in
                (uu____3813, White) in
              deps_add_dep dep_graph file_name uu____3808);
             (let uu____3818 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3818))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3851 =
           let uu____3856 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3856 in
         match uu____3851 with
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
                   (let uu____3875 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3875);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3881 =
                      let uu____3884 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3884 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3881))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4087 = topological_dependences_of all_cmd_line_files in
      (uu____4087, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4100  ->
    fun f  ->
      match uu____4100 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4121  ->
    fun fn  ->
      match uu____4121 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4140 = FStar_Options.debug_any () in
             if uu____4140
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4147 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4147
            then
              let uu____4150 =
                let uu____4151 =
                  let uu____4152 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4152 in
                digest_of_file1 uu____4151 in
              [uu____4150]
            else [] in
          let binary_deps =
            let uu____4159 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4159
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4169 =
                      (is_interface fn1) &&
                        (let uu____4171 = lowercase_module_name fn1 in
                         uu____4171 = module_name) in
                    Prims.op_Negation uu____4169)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___122_4189 =
            match uu___122_4189 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4209 =
                    let uu____4212 = digest_of_file1 fn2 in uu____4212 :: out in
                  hash_deps uu____4209 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4218  ->
    match uu____4218 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4238 =
                  let uu____4243 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4243 FStar_Option.get in
                match uu____4238 with
                | (f_deps,uu____4265) ->
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
  fun uu____4276  ->
    match uu____4276 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4302 =
                   let uu____4307 = deps_try_find deps f in
                   FStar_All.pipe_right uu____4307 FStar_Option.get in
                 match uu____4302 with
                 | (f_deps,uu____4329) ->
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps in
                     let files1 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files in
                     ((let uu____4339 = is_interface f in
                       if uu____4339
                       then
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" f f
                           (FStar_String.concat "\\\n\t" files1)
                       else ());
                      FStar_Util.print3 "%s.checked: %s \\\n\t%s\n\n" f f
                        (FStar_String.concat " \\\n\t" files1);
                      (let uu____4342 = is_implementation f in
                       if uu____4342
                       then
                         let ml_base_name =
                           let uu____4344 =
                             let uu____4345 =
                               let uu____4348 = FStar_Util.basename f in
                               check_and_strip_suffix uu____4348 in
                             FStar_Option.get uu____4345 in
                           FStar_Util.replace_chars uu____4344 46 "_" in
                         let uu____4349 =
                           let uu____4350 = FStar_Options.output_dir () in
                           match uu____4350 with
                           | FStar_Pervasives_Native.None  -> ""
                           | FStar_Pervasives_Native.Some x ->
                               Prims.strcat x "/" in
                         FStar_Util.print3 "%s%s.ml: %s.checked\n\n"
                           uu____4349 ml_base_name f
                       else ()))));
         (let all_fst_files =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
          let uu____4362 =
            FStar_All.pipe_right all_fst_files
              (FStar_String.concat " \\\n\t") in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n" uu____4362))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4368 = FStar_Options.dep () in
    match uu____4368 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4371 = deps in
        (match uu____4371 with
         | Mk (deps1,uu____4373,uu____4374) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4379 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()