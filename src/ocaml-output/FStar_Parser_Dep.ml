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
let file_of_dep:
  files_for_module_name -> file_name Prims.list -> dependence -> file_name =
  fun file_system_map  ->
    fun all_cmd_line_files  ->
      fun d  ->
        let cmd_line_has_impl key =
          FStar_All.pipe_right all_cmd_line_files
            (FStar_Util.for_some
               (fun fn  ->
                  (is_implementation fn) &&
                    (let uu____699 = lowercase_module_name fn in
                     key = uu____699))) in
        match d with
        | UseInterface key ->
            let uu____701 = interface_of file_system_map key in
            (match uu____701 with
             | FStar_Pervasives_Native.None  ->
                 let uu____707 =
                   let uu____708 =
                     FStar_Util.format1
                       "Expected an interface for module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____708 in
                 FStar_Exn.raise uu____707
             | FStar_Pervasives_Native.Some f -> f)
        | PreferInterface key when
            (let uu____713 = cmd_line_has_impl key in
             Prims.op_Negation uu____713) &&
              (has_interface file_system_map key)
            ->
            let uu____714 = interface_of file_system_map key in
            FStar_All.pipe_left FStar_Option.get uu____714
        | PreferInterface key ->
            let uu____720 = implementation_of file_system_map key in
            (match uu____720 with
             | FStar_Pervasives_Native.None  ->
                 let uu____726 =
                   let uu____727 =
                     FStar_Util.format1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____727 in
                 FStar_Exn.raise uu____726
             | FStar_Pervasives_Native.Some f -> f)
        | UseImplementation key ->
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
             | FStar_Pervasives_Native.Some f -> f)
let dependences_of:
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list
  =
  fun file_system_map  ->
    fun deps  ->
      fun all_cmd_line_files  ->
        fun fn  ->
          let uu____759 = deps_try_find deps fn in
          match uu____759 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____773) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____804 to_1 =
          match uu____804 with
          | (d,color) ->
              let uu____824 = is_interface to_1 in
              if uu____824
              then
                let uu____831 =
                  let uu____834 =
                    let uu____835 = lowercase_module_name to_1 in
                    PreferInterface uu____835 in
                  uu____834 :: d in
                (uu____831, color)
              else
                (let uu____839 =
                   let uu____842 =
                     let uu____843 = lowercase_module_name to_1 in
                     UseImplementation uu____843 in
                   uu____842 :: d in
                 (uu____839, color)) in
        let uu____846 = deps_try_find deps from in
        match uu____846 with
        | FStar_Pervasives_Native.None  ->
            let uu____857 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____857
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____873 = add_dep key_deps to_ in
            deps_add_dep deps from uu____873
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____884 =
       let uu____885 =
         let uu____886 =
           let uu____887 =
             let uu____890 =
               let uu____893 = deps_keys graph in FStar_List.unique uu____893 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____902 =
                      let uu____907 = deps_try_find graph k in
                      FStar_Util.must uu____907 in
                    FStar_Pervasives_Native.fst uu____902 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____890 in
           FStar_String.concat "\n" uu____887 in
         Prims.strcat uu____886 "\n}\n" in
       Prims.strcat "digraph {\n" uu____885 in
     FStar_Util.write_file "dep.graph" uu____884)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____934  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____951 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____951 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____977 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____977
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____998 =
              let uu____999 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____999 in
            FStar_Exn.raise uu____998)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1039 = FStar_Util.smap_try_find map1 key in
      match uu____1039 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1076 = is_interface full_path in
          if uu____1076
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1110 = is_interface full_path in
          if uu____1110
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1137 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1151  ->
          match uu____1151 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1137);
    FStar_List.iter
      (fun f  ->
         let uu____1162 = lowercase_module_name f in add_entry uu____1162 f)
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
        (let uu____1177 =
           let uu____1180 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1180 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1206 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1206 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1177);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1378 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1378 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1389 = string_of_lid l last1 in
      FStar_String.lowercase uu____1389
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1393 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1393
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1403 =
        let uu____1404 =
          let uu____1405 =
            let uu____1406 =
              let uu____1409 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1409 in
            FStar_Util.must uu____1406 in
          FStar_String.lowercase uu____1405 in
        uu____1404 <> k' in
      if uu____1403
      then
        let uu____1410 =
          let uu____1411 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1411 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1410
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1416 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1430 = FStar_Options.prims_basename () in
      let uu____1431 =
        let uu____1434 = FStar_Options.pervasives_basename () in
        let uu____1435 =
          let uu____1438 = FStar_Options.pervasives_native_basename () in
          [uu____1438] in
        uu____1434 :: uu____1435 in
      uu____1430 :: uu____1431 in
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
        let uu____1849 =
          let uu____1850 =
            let uu____1851 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1851 in
          Prims.op_Negation uu____1850 in
        if uu____1849
        then
          let uu____2002 =
            let uu____2005 = FStar_ST.op_Bang deps1 in d :: uu____2005 in
          FStar_ST.op_Colon_Equals deps1 uu____2002
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge lid =
        let key = lowercase_join_longident lid true in
        let uu____2325 = resolve_module_name working_map key in
        match uu____2325 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2352 =
                (has_interface working_map module_name) &&
                  (has_implementation working_map module_name) in
              if uu____2352
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2375 -> false in
      let record_open_module let_open lid =
        let uu____2385 = add_dependence_edge lid in
        if uu____2385
        then true
        else
          (if let_open
           then
             (let uu____2388 =
                let uu____2389 = string_of_lid lid true in
                FStar_Util.format1 "Module not found: %s" uu____2389 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2388)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2397 =
            let uu____2398 = string_of_lid lid true in
            FStar_Util.format1
              "No modules in namespace %s and no file with that name either"
              uu____2398 in
          FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2397
        else () in
      let record_open let_open lid =
        let uu____2407 = record_open_module let_open lid in
        if uu____2407
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2417 =
        match uu____2417 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2424 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2434 = FStar_Util.smap_try_find original_map alias in
        match uu____2434 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2486 =
              FStar_Util.format1 "module not found in search path: %s\n"
                alias in
            FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2486 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2491 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2495 = add_dependence_edge module_name in
            if uu____2495
            then ()
            else
              (let uu____2497 = FStar_Options.debug_any () in
               if uu____2497
               then
                 let uu____2498 =
                   let uu____2499 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2499 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2498
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___114_2585 =
         match uu___114_2585 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2594 =
                   let uu____2595 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2595 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2599) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2606 =
                   let uu____2607 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2607 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___115_2616 =
         match uu___115_2616 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2622 =
                 let uu____2623 = lowercase_join_longident lid true in
                 PreferInterface uu____2623 in
               add_dep deps uu____2622);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2645,patterms) ->
             FStar_List.iter
               (fun uu____2667  ->
                  match uu____2667 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2676,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2678;
               FStar_Parser_AST.mdest = uu____2679;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2681;
               FStar_Parser_AST.mdest = uu____2682;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2684,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2686;
               FStar_Parser_AST.mdest = uu____2687;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2691,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2721  -> match uu____2721 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2734,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2741 -> ()
         | FStar_Parser_AST.Pragma uu____2742 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2766 =
                 let uu____2767 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2767 > (Prims.parse_int "1") in
               if uu____2766
               then
                 let uu____2828 =
                   let uu____2829 =
                     let uu____2834 =
                       let uu____2835 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2835 in
                     (uu____2834, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2829 in
                 FStar_Exn.raise uu____2828
               else ()))
       and collect_tycon uu___116_2837 =
         match uu___116_2837 with
         | FStar_Parser_AST.TyconAbstract (uu____2838,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2850,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2864,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2910  ->
                   match uu____2910 with
                   | (uu____2919,t,uu____2921) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2926,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2985  ->
                   match uu____2985 with
                   | (uu____2998,t,uu____3000,uu____3001) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___117_3010 =
         match uu___117_3010 with
         | FStar_Parser_AST.DefineEffect (uu____3011,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3025,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___118_3036 =
         match uu___118_3036 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3037,t);
             FStar_Parser_AST.brange = uu____3039;
             FStar_Parser_AST.blevel = uu____3040;
             FStar_Parser_AST.aqual = uu____3041;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3042,t);
             FStar_Parser_AST.brange = uu____3044;
             FStar_Parser_AST.blevel = uu____3045;
             FStar_Parser_AST.aqual = uu____3046;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3048;
             FStar_Parser_AST.blevel = uu____3049;
             FStar_Parser_AST.aqual = uu____3050;_} -> collect_term t
         | uu____3051 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___119_3053 =
         match uu___119_3053 with
         | FStar_Const.Const_int
             (uu____3054,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3069 =
               let uu____3070 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3070 in
             add_dep deps uu____3069
         | FStar_Const.Const_char uu____3092 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3114 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3136 -> ()
       and collect_term' uu___120_3137 =
         match uu___120_3137 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3146 =
                   let uu____3147 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3147 in
                 collect_term' uu____3146)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3149 -> ()
         | FStar_Parser_AST.Uvar uu____3150 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3153) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3183  ->
                   match uu____3183 with | (t,uu____3189) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3199) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3201,patterms,t) ->
             (FStar_List.iter
                (fun uu____3225  ->
                   match uu____3225 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3236,t1,t2) ->
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
                (fun uu____3332  ->
                   match uu____3332 with | (uu____3337,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3340) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3396,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3399,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3402) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3408) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3414,uu____3415) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___121_3423 =
         match uu___121_3423 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3424 -> ()
         | FStar_Parser_AST.PatConst uu____3425 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3433 -> ()
         | FStar_Parser_AST.PatName uu____3440 -> ()
         | FStar_Parser_AST.PatTvar uu____3441 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3455) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3474  ->
                  match uu____3474 with | (uu____3479,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3503 =
         match uu____3503 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3521 = FStar_Parser_Driver.parse_file filename in
       match uu____3521 with
       | (ast,uu____3541) ->
           (collect_module ast;
            (let uu____3555 = FStar_ST.op_Bang deps in
             let uu____3622 = FStar_ST.op_Bang mo_roots in
             (uu____3555, uu____3622))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3718 =
        let uu____3719 = deps_try_find dep_graph file_name in
        uu____3719 = FStar_Pervasives_Native.None in
      if uu____3718
      then
        let uu____3736 = collect_one file_system_map file_name in
        match uu____3736 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3759 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3759
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3764 =
                let uu____3769 = FStar_List.unique deps1 in
                (uu____3769, White) in
              deps_add_dep dep_graph file_name uu____3764);
             (let uu____3774 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3774))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3807 =
           let uu____3812 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3812 in
         match uu____3807 with
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
                   (let uu____3831 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3831);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3837 =
                      let uu____3840 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3840 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3837))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4043 = topological_dependences_of all_cmd_line_files in
      (uu____4043, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4056  ->
    fun f  ->
      match uu____4056 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let checked_file_name = Prims.strcat fn ".checked" in
    let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
    let lax_ok =
      let uu____4075 = FStar_Options.should_verify_file fn in
      Prims.op_Negation uu____4075 in
    if lax_ok then lax_checked_file_name else checked_file_name
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4085  ->
    fun fn  ->
      match uu____4085 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4104 = FStar_Options.debug_any () in
             if uu____4104
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4111 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4111
            then
              let uu____4114 =
                let uu____4115 =
                  let uu____4116 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4116 in
                digest_of_file1 uu____4115 in
              [uu____4114]
            else [] in
          let binary_deps =
            let uu____4123 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4123
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4133 =
                      (is_interface fn1) &&
                        (let uu____4135 = lowercase_module_name fn1 in
                         uu____4135 = module_name) in
                    Prims.op_Negation uu____4133)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___122_4153 =
            match uu___122_4153 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4173 =
                    let uu____4176 = digest_of_file1 fn2 in uu____4176 :: out in
                  hash_deps uu____4173 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4182  ->
    match uu____4182 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4202 =
                  let uu____4207 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4207 FStar_Option.get in
                match uu____4202 with
                | (f_deps,uu____4229) ->
                    let files =
                      FStar_List.map
                        (file_of_dep file_system_map all_cmd_line_files)
                        f_deps in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files in
                    FStar_Util.print2 "%s: %s\n" f
                      (FStar_String.concat " " files1)))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4241 = FStar_Options.dep () in
    match uu____4241 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4244 = deps in
        (match uu____4244 with
         | Mk (deps1,uu____4246,uu____4247) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4252 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()