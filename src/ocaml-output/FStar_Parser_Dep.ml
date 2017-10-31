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
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____191 =
      let uu____194 = FStar_Util.basename f in
      check_and_strip_suffix uu____194 in
    match uu____191 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____196 =
          let uu____197 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____197 in
        FStar_Exn.raise uu____196
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____214 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____226 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____238 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____249 . Prims.unit -> 'Auu____249 Prims.list =
  fun uu____252  -> []
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
  fun uu____341  ->
    fun k  -> match uu____341 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____370  ->
    fun k  ->
      fun v1  -> match uu____370 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____392  -> match uu____392 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____408  ->
    let uu____409 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____409
let empty_deps: deps =
  let uu____420 =
    let uu____429 = deps_empty () in
    let uu____430 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____429, uu____430, []) in
  Mk uu____420
let module_name_of_dep: dependence -> module_name =
  fun uu___113_463  ->
    match uu___113_463 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____477 = FStar_Util.smap_try_find file_system_map key in
      match uu____477 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____499) ->
          let uu____514 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____514
      | FStar_Pervasives_Native.Some
          (uu____515,FStar_Pervasives_Native.Some fn) ->
          let uu____531 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____531
      | uu____532 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____553 = FStar_Util.smap_try_find file_system_map key in
      match uu____553 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____575) ->
          FStar_Pervasives_Native.Some iface
      | uu____590 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____611 = FStar_Util.smap_try_find file_system_map key in
      match uu____611 with
      | FStar_Pervasives_Native.Some
          (uu____632,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____648 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____665 = interface_of file_system_map key in
      FStar_Option.isSome uu____665
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____674 = implementation_of file_system_map key in
      FStar_Option.isSome uu____674
let cache_file_name: Prims.string -> Prims.string =
  fun fn  -> Prims.strcat fn ".checked"
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
                      (let uu____705 = lowercase_module_name fn in
                       key = uu____705))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____712 = interface_of file_system_map key in
              (match uu____712 with
               | FStar_Pervasives_Native.None  ->
                   let uu____718 =
                     let uu____719 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____719 in
                   FStar_Exn.raise uu____718
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when
              (let uu____724 = cmd_line_has_impl key in
               Prims.op_Negation uu____724) &&
                (has_interface file_system_map key)
              ->
              let uu____725 =
                let uu____726 = interface_of file_system_map key in
                FStar_Option.get uu____726 in
              maybe_add_suffix uu____725
          | PreferInterface key ->
              let uu____730 = implementation_of file_system_map key in
              (match uu____730 with
               | FStar_Pervasives_Native.None  ->
                   let uu____736 =
                     let uu____737 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____737 in
                   FStar_Exn.raise uu____736
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____740 = implementation_of file_system_map key in
              (match uu____740 with
               | FStar_Pervasives_Native.None  ->
                   let uu____746 =
                     let uu____747 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____747 in
                   FStar_Exn.raise uu____746
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
          let uu____777 = deps_try_find deps fn in
          match uu____777 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____791) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____822 to_1 =
          match uu____822 with
          | (d,color) ->
              let uu____842 = is_interface to_1 in
              if uu____842
              then
                let uu____849 =
                  let uu____852 =
                    let uu____853 = lowercase_module_name to_1 in
                    PreferInterface uu____853 in
                  uu____852 :: d in
                (uu____849, color)
              else
                (let uu____857 =
                   let uu____860 =
                     let uu____861 = lowercase_module_name to_1 in
                     UseImplementation uu____861 in
                   uu____860 :: d in
                 (uu____857, color)) in
        let uu____864 = deps_try_find deps from in
        match uu____864 with
        | FStar_Pervasives_Native.None  ->
            let uu____875 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____875
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____891 = add_dep key_deps to_ in
            deps_add_dep deps from uu____891
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____902 =
       let uu____903 =
         let uu____904 =
           let uu____905 =
             let uu____908 =
               let uu____911 = deps_keys graph in FStar_List.unique uu____911 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____920 =
                      let uu____925 = deps_try_find graph k in
                      FStar_Util.must uu____925 in
                    FStar_Pervasives_Native.fst uu____920 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____908 in
           FStar_String.concat "\n" uu____905 in
         Prims.strcat uu____904 "\n}\n" in
       Prims.strcat "digraph {\n" uu____903 in
     FStar_Util.write_file "dep.graph" uu____902)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____952  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____969 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____969 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____995 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____995
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1016 =
              let uu____1017 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____1017 in
            FStar_Exn.raise uu____1016)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1057 = FStar_Util.smap_try_find map1 key in
      match uu____1057 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1094 = is_interface full_path in
          if uu____1094
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1128 = is_interface full_path in
          if uu____1128
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1155 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1169  ->
          match uu____1169 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1155);
    FStar_List.iter
      (fun f  ->
         let uu____1180 = lowercase_module_name f in add_entry uu____1180 f)
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
        (let uu____1195 =
           let uu____1198 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1198 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1224 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1224 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1195);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1396 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1396 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1407 = string_of_lid l last1 in
      FStar_String.lowercase uu____1407
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1411 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1411
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1421 =
        let uu____1422 =
          let uu____1423 =
            let uu____1424 =
              let uu____1427 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1427 in
            FStar_Util.must uu____1424 in
          FStar_String.lowercase uu____1423 in
        uu____1422 <> k' in
      if uu____1421
      then
        let uu____1428 =
          let uu____1429 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1429 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1428
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1434 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1448 = FStar_Options.prims_basename () in
      let uu____1449 =
        let uu____1452 = FStar_Options.pervasives_basename () in
        let uu____1453 =
          let uu____1456 = FStar_Options.pervasives_native_basename () in
          [uu____1456] in
        uu____1452 :: uu____1453 in
      uu____1448 :: uu____1449 in
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
        let uu____1867 =
          let uu____1868 =
            let uu____1869 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1869 in
          Prims.op_Negation uu____1868 in
        if uu____1867
        then
          let uu____2020 =
            let uu____2023 = FStar_ST.op_Bang deps1 in d :: uu____2023 in
          FStar_ST.op_Colon_Equals deps1 uu____2020
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge lid =
        let key = lowercase_join_longident lid true in
        let uu____2343 = resolve_module_name working_map key in
        match uu____2343 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2370 =
                (has_interface working_map module_name) &&
                  (has_implementation working_map module_name) in
              if uu____2370
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2393 -> false in
      let record_open_module let_open lid =
        let uu____2403 = add_dependence_edge lid in
        if uu____2403
        then true
        else
          (if let_open
           then
             (let uu____2406 =
                let uu____2407 = string_of_lid lid true in
                FStar_Util.format1 "Module not found: %s" uu____2407 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2406)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2415 =
            let uu____2416 = string_of_lid lid true in
            FStar_Util.format1
              "No modules in namespace %s and no file with that name either"
              uu____2416 in
          FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2415
        else () in
      let record_open let_open lid =
        let uu____2425 = record_open_module let_open lid in
        if uu____2425
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2435 =
        match uu____2435 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2442 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2452 = FStar_Util.smap_try_find original_map alias in
        match uu____2452 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2504 =
              FStar_Util.format1 "module not found in search path: %s\n"
                alias in
            FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2504 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2509 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2513 = add_dependence_edge module_name in
            if uu____2513
            then ()
            else
              (let uu____2515 = FStar_Options.debug_any () in
               if uu____2515
               then
                 let uu____2516 =
                   let uu____2517 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2517 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2516
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___114_2603 =
         match uu___114_2603 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2612 =
                   let uu____2613 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2613 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2617) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2624 =
                   let uu____2625 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2625 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___115_2634 =
         match uu___115_2634 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2640 =
                 let uu____2641 = lowercase_join_longident lid true in
                 PreferInterface uu____2641 in
               add_dep deps uu____2640);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2663,patterms) ->
             FStar_List.iter
               (fun uu____2685  ->
                  match uu____2685 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2694,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2696;
               FStar_Parser_AST.mdest = uu____2697;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2699;
               FStar_Parser_AST.mdest = uu____2700;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2702,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2704;
               FStar_Parser_AST.mdest = uu____2705;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2709,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2739  -> match uu____2739 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2752,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2759 -> ()
         | FStar_Parser_AST.Pragma uu____2760 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2784 =
                 let uu____2785 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2785 > (Prims.parse_int "1") in
               if uu____2784
               then
                 let uu____2846 =
                   let uu____2847 =
                     let uu____2852 =
                       let uu____2853 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2853 in
                     (uu____2852, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2847 in
                 FStar_Exn.raise uu____2846
               else ()))
       and collect_tycon uu___116_2855 =
         match uu___116_2855 with
         | FStar_Parser_AST.TyconAbstract (uu____2856,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2868,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2882,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2928  ->
                   match uu____2928 with
                   | (uu____2937,t,uu____2939) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2944,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3003  ->
                   match uu____3003 with
                   | (uu____3016,t,uu____3018,uu____3019) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___117_3028 =
         match uu___117_3028 with
         | FStar_Parser_AST.DefineEffect (uu____3029,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3043,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___118_3054 =
         match uu___118_3054 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3055,t);
             FStar_Parser_AST.brange = uu____3057;
             FStar_Parser_AST.blevel = uu____3058;
             FStar_Parser_AST.aqual = uu____3059;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3060,t);
             FStar_Parser_AST.brange = uu____3062;
             FStar_Parser_AST.blevel = uu____3063;
             FStar_Parser_AST.aqual = uu____3064;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3066;
             FStar_Parser_AST.blevel = uu____3067;
             FStar_Parser_AST.aqual = uu____3068;_} -> collect_term t
         | uu____3069 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___119_3071 =
         match uu___119_3071 with
         | FStar_Const.Const_int
             (uu____3072,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3087 =
               let uu____3088 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3088 in
             add_dep deps uu____3087
         | FStar_Const.Const_char uu____3110 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3132 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3154 -> ()
       and collect_term' uu___120_3155 =
         match uu___120_3155 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3164 =
                   let uu____3165 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3165 in
                 collect_term' uu____3164)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3167 -> ()
         | FStar_Parser_AST.Uvar uu____3168 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3171) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3201  ->
                   match uu____3201 with | (t,uu____3207) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3217) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3219,patterms,t) ->
             (FStar_List.iter
                (fun uu____3243  ->
                   match uu____3243 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3254,t1,t2) ->
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
                (fun uu____3350  ->
                   match uu____3350 with | (uu____3355,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3358) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3414,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3417,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3420) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3426) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3432,uu____3433) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___121_3441 =
         match uu___121_3441 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3442 -> ()
         | FStar_Parser_AST.PatConst uu____3443 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3451 -> ()
         | FStar_Parser_AST.PatName uu____3458 -> ()
         | FStar_Parser_AST.PatTvar uu____3459 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3473) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3492  ->
                  match uu____3492 with | (uu____3497,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3521 =
         match uu____3521 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3539 = FStar_Parser_Driver.parse_file filename in
       match uu____3539 with
       | (ast,uu____3559) ->
           (collect_module ast;
            (let uu____3573 = FStar_ST.op_Bang deps in
             let uu____3640 = FStar_ST.op_Bang mo_roots in
             (uu____3573, uu____3640))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3736 =
        let uu____3737 = deps_try_find dep_graph file_name in
        uu____3737 = FStar_Pervasives_Native.None in
      if uu____3736
      then
        let uu____3754 = collect_one file_system_map file_name in
        match uu____3754 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3777 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3777
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3782 =
                let uu____3787 = FStar_List.unique deps1 in
                (uu____3787, White) in
              deps_add_dep dep_graph file_name uu____3782);
             (let uu____3792 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3792))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3825 =
           let uu____3830 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3830 in
         match uu____3825 with
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
                   (let uu____3849 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3849);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3855 =
                      let uu____3858 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3858 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3855))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4061 = topological_dependences_of all_cmd_line_files in
      (uu____4061, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4074  ->
    fun f  ->
      match uu____4074 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4095  ->
    fun fn  ->
      match uu____4095 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4114 = FStar_Options.debug_any () in
             if uu____4114
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4121 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4121
            then
              let uu____4124 =
                let uu____4125 =
                  let uu____4126 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4126 in
                digest_of_file1 uu____4125 in
              [uu____4124]
            else [] in
          let binary_deps =
            let uu____4133 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4133
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4143 =
                      (is_interface fn1) &&
                        (let uu____4145 = lowercase_module_name fn1 in
                         uu____4145 = module_name) in
                    Prims.op_Negation uu____4143)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___122_4163 =
            match uu___122_4163 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4183 =
                    let uu____4186 = digest_of_file1 fn2 in uu____4186 :: out in
                  hash_deps uu____4183 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4192  ->
    match uu____4192 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4217 =
                  let uu____4222 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4222 FStar_Option.get in
                match uu____4217 with
                | (f_deps,uu____4244) ->
                    let files =
                      FStar_List.map
                        (file_of_dep_aux true file_system_map
                           all_cmd_line_files) f_deps in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files in
                    ((let uu____4254 = is_interface f in
                      if uu____4254
                      then
                        FStar_Util.print2 "%s:\\\n\t%s\n\n" f
                          (FStar_String.concat "\\\n\t" files1)
                      else ());
                     FStar_Util.print3 "%s.checked: %s \\\n\t%s\n\n" f f
                       (FStar_String.concat "\\\n\t" files1);
                     (let uu____4257 = is_implementation f in
                      if uu____4257
                      then
                        let ml_base_name =
                          let uu____4259 =
                            let uu____4260 =
                              let uu____4263 = FStar_Util.basename f in
                              check_and_strip_suffix uu____4263 in
                            FStar_Option.get uu____4260 in
                          FStar_Util.replace_chars uu____4259 46 "_" in
                        let uu____4264 =
                          let uu____4265 = FStar_Options.output_dir () in
                          match uu____4265 with
                          | FStar_Pervasives_Native.None  -> ""
                          | FStar_Pervasives_Native.Some x ->
                              Prims.strcat x "/" in
                        FStar_Util.print3 "%s%s.ml: %s.checked\n\n"
                          uu____4264 ml_base_name f
                      else ()))))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4273 = FStar_Options.dep () in
    match uu____4273 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4276 = deps in
        (match uu____4276 with
         | Mk (deps1,uu____4278,uu____4279) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4284 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()