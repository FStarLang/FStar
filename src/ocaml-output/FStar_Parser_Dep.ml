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
                 let uu____704 =
                   let uu____705 =
                     FStar_Util.format1
                       "Expected an interface for module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____705 in
                 FStar_Exn.raise uu____704
             | FStar_Pervasives_Native.Some f -> f)
        | PreferInterface key when
            (let uu____710 = cmd_line_has_impl key in
             Prims.op_Negation uu____710) &&
              (has_interface file_system_map key)
            ->
            let uu____711 = interface_of file_system_map key in
            FStar_All.pipe_left FStar_Option.get uu____711
        | PreferInterface key ->
            let uu____717 = implementation_of file_system_map key in
            (match uu____717 with
             | FStar_Pervasives_Native.None  ->
                 let uu____720 =
                   let uu____721 =
                     FStar_Util.format1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____721 in
                 FStar_Exn.raise uu____720
             | FStar_Pervasives_Native.Some f -> f)
        | UseImplementation key ->
            let uu____724 = implementation_of file_system_map key in
            (match uu____724 with
             | FStar_Pervasives_Native.None  ->
                 let uu____727 =
                   let uu____728 =
                     FStar_Util.format1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____728 in
                 FStar_Exn.raise uu____727
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
          let uu____750 = deps_try_find deps fn in
          match uu____750 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____764) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____795 to_1 =
          match uu____795 with
          | (d,color) ->
              let uu____815 = is_interface to_1 in
              if uu____815
              then
                let uu____822 =
                  let uu____825 =
                    let uu____826 = lowercase_module_name to_1 in
                    PreferInterface uu____826 in
                  uu____825 :: d in
                (uu____822, color)
              else
                (let uu____830 =
                   let uu____833 =
                     let uu____834 = lowercase_module_name to_1 in
                     UseImplementation uu____834 in
                   uu____833 :: d in
                 (uu____830, color)) in
        let uu____837 = deps_try_find deps from in
        match uu____837 with
        | FStar_Pervasives_Native.None  ->
            let uu____848 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____848
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____864 = add_dep key_deps to_ in
            deps_add_dep deps from uu____864
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____875 =
       let uu____876 =
         let uu____877 =
           let uu____878 =
             let uu____881 =
               let uu____884 = deps_keys graph in FStar_List.unique uu____884 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____893 =
                      let uu____898 = deps_try_find graph k in
                      FStar_Util.must uu____898 in
                    FStar_Pervasives_Native.fst uu____893 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____881 in
           FStar_String.concat "\n" uu____878 in
         Prims.strcat uu____877 "\n}\n" in
       Prims.strcat "digraph {\n" uu____876 in
     FStar_Util.write_file "dep.graph" uu____875)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____925  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____942 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____942 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____968 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____968
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____989 =
              let uu____990 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____990 in
            FStar_Exn.raise uu____989)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1030 = FStar_Util.smap_try_find map1 key in
      match uu____1030 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1067 = is_interface full_path in
          if uu____1067
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1101 = is_interface full_path in
          if uu____1101
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1128 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1142  ->
          match uu____1142 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1128);
    FStar_List.iter
      (fun f  ->
         let uu____1153 = lowercase_module_name f in add_entry uu____1153 f)
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
        (let uu____1168 =
           let uu____1171 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1171 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1197 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1197 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1168);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1369 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1369 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1380 = string_of_lid l last1 in
      FStar_String.lowercase uu____1380
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1384 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1384
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1394 =
        let uu____1395 =
          let uu____1396 =
            let uu____1397 =
              let uu____1400 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1400 in
            FStar_Util.must uu____1397 in
          FStar_String.lowercase uu____1396 in
        uu____1395 <> k' in
      if uu____1394
      then
        let uu____1401 =
          let uu____1402 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1402 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1401
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1407 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1421 = FStar_Options.prims_basename () in
      let uu____1422 =
        let uu____1425 = FStar_Options.pervasives_basename () in
        let uu____1426 =
          let uu____1429 = FStar_Options.pervasives_native_basename () in
          [uu____1429] in
        uu____1425 :: uu____1426 in
      uu____1421 :: uu____1422 in
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
        let uu____1840 =
          let uu____1841 =
            let uu____1842 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1842 in
          Prims.op_Negation uu____1841 in
        if uu____1840
        then
          let uu____1993 =
            let uu____1996 = FStar_ST.op_Bang deps1 in d :: uu____1996 in
          FStar_ST.op_Colon_Equals deps1 uu____1993
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge lid =
        let key = lowercase_join_longident lid true in
        let uu____2316 = resolve_module_name working_map key in
        match uu____2316 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2343 =
                (has_interface working_map module_name) &&
                  (has_implementation working_map module_name) in
              if uu____2343
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2366 -> false in
      let record_open_module let_open lid =
        let uu____2376 = add_dependence_edge lid in
        if uu____2376
        then true
        else
          (let key = lowercase_join_longident lid true in
           let r = enter_namespace original_map working_map key in
           if Prims.op_Negation r
           then
             (if let_open
              then
                FStar_Exn.raise
                  (FStar_Errors.Error
                     ("let-open only supported for modules, not namespaces",
                       (FStar_Ident.range_of_lid lid)))
              else
                (let uu____2382 =
                   let uu____2383 = string_of_lid lid true in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____2383 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2382))
           else ();
           false) in
      let record_open_namespace error_msg lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          match error_msg with
          | FStar_Pervasives_Native.Some e ->
              FStar_Exn.raise
                (FStar_Errors.Error (e, (FStar_Ident.range_of_lid lid)))
          | FStar_Pervasives_Native.None  ->
              let uu____2399 =
                let uu____2400 = string_of_lid lid true in
                FStar_Util.format1
                  "No modules in namespace %s and no file with that name either"
                  uu____2400 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2399
        else () in
      let record_open let_open lid =
        let uu____2409 = record_open_module let_open lid in
        if uu____2409
        then ()
        else
          (let msg =
             if let_open
             then
               FStar_Pervasives_Native.Some
                 "let-open only supported for modules, not namespaces"
             else FStar_Pervasives_Native.None in
           record_open_namespace msg lid) in
      let record_open_module_or_namespace uu____2424 =
        match uu____2424 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  ->
                 record_open_namespace FStar_Pervasives_Native.None lid
             | Open_module  ->
                 let uu____2431 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2441 = FStar_Util.smap_try_find original_map alias in
        match uu____2441 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2493 =
              let uu____2494 =
                let uu____2499 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias in
                (uu____2499, (FStar_Ident.range_of_lid lid)) in
              FStar_Errors.Error uu____2494 in
            FStar_Exn.raise uu____2493 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2504 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2508 = add_dependence_edge module_name in
            if uu____2508
            then ()
            else
              (let uu____2510 = FStar_Options.debug_any () in
               if uu____2510
               then
                 let uu____2511 =
                   let uu____2512 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2512 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2511
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___114_2598 =
         match uu___114_2598 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2607 =
                   let uu____2608 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2608 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2612) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2619 =
                   let uu____2620 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2620 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___115_2629 =
         match uu___115_2629 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2635 =
                 let uu____2636 = lowercase_join_longident lid true in
                 PreferInterface uu____2636 in
               add_dep deps uu____2635);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2658,patterms) ->
             FStar_List.iter
               (fun uu____2680  ->
                  match uu____2680 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2689,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2691;
               FStar_Parser_AST.mdest = uu____2692;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2694;
               FStar_Parser_AST.mdest = uu____2695;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2697,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2699;
               FStar_Parser_AST.mdest = uu____2700;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2704,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2734  -> match uu____2734 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2747,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2754 -> ()
         | FStar_Parser_AST.Pragma uu____2755 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2779 =
                 let uu____2780 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2780 > (Prims.parse_int "1") in
               if uu____2779
               then
                 let uu____2841 =
                   let uu____2842 =
                     let uu____2847 =
                       let uu____2848 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2848 in
                     (uu____2847, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2842 in
                 FStar_Exn.raise uu____2841
               else ()))
       and collect_tycon uu___116_2850 =
         match uu___116_2850 with
         | FStar_Parser_AST.TyconAbstract (uu____2851,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2863,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2877,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2923  ->
                   match uu____2923 with
                   | (uu____2932,t,uu____2934) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2939,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2998  ->
                   match uu____2998 with
                   | (uu____3011,t,uu____3013,uu____3014) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___117_3023 =
         match uu___117_3023 with
         | FStar_Parser_AST.DefineEffect (uu____3024,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3038,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___118_3049 =
         match uu___118_3049 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3050,t);
             FStar_Parser_AST.brange = uu____3052;
             FStar_Parser_AST.blevel = uu____3053;
             FStar_Parser_AST.aqual = uu____3054;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3055,t);
             FStar_Parser_AST.brange = uu____3057;
             FStar_Parser_AST.blevel = uu____3058;
             FStar_Parser_AST.aqual = uu____3059;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3061;
             FStar_Parser_AST.blevel = uu____3062;
             FStar_Parser_AST.aqual = uu____3063;_} -> collect_term t
         | uu____3064 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___119_3066 =
         match uu___119_3066 with
         | FStar_Const.Const_int
             (uu____3067,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3082 =
               let uu____3083 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3083 in
             add_dep deps uu____3082
         | FStar_Const.Const_char uu____3105 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3127 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3149 -> ()
       and collect_term' uu___120_3150 =
         match uu___120_3150 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3159 =
                   let uu____3160 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3160 in
                 collect_term' uu____3159)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3162 -> ()
         | FStar_Parser_AST.Uvar uu____3163 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3166) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3196  ->
                   match uu____3196 with | (t,uu____3202) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3212) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3214,patterms,t) ->
             (FStar_List.iter
                (fun uu____3238  ->
                   match uu____3238 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3249,t1,t2) ->
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
                (fun uu____3345  ->
                   match uu____3345 with | (uu____3350,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3353) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3409,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3412,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3415) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3421) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3427,uu____3428) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___121_3436 =
         match uu___121_3436 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3437 -> ()
         | FStar_Parser_AST.PatConst uu____3438 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3446 -> ()
         | FStar_Parser_AST.PatName uu____3453 -> ()
         | FStar_Parser_AST.PatTvar uu____3454 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3468) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3487  ->
                  match uu____3487 with | (uu____3492,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3516 =
         match uu____3516 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3534 = FStar_Parser_Driver.parse_file filename in
       match uu____3534 with
       | (ast,uu____3554) ->
           (collect_module ast;
            (let uu____3568 = FStar_ST.op_Bang deps in
             let uu____3635 = FStar_ST.op_Bang mo_roots in
             (uu____3568, uu____3635))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3731 =
        let uu____3732 = deps_try_find dep_graph file_name in
        uu____3732 = FStar_Pervasives_Native.None in
      if uu____3731
      then
        let uu____3749 = collect_one file_system_map file_name in
        match uu____3749 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3772 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3772
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3777 =
                let uu____3782 = FStar_List.unique deps1 in
                (uu____3782, White) in
              deps_add_dep dep_graph file_name uu____3777);
             (let uu____3787 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3787))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3820 =
           let uu____3825 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3825 in
         match uu____3820 with
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
                   (let uu____3844 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3844);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3850 =
                      let uu____3853 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3853 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3850))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4056 = topological_dependences_of all_cmd_line_files in
      (uu____4056, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4069  ->
    fun f  ->
      match uu____4069 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let checked_file_name = Prims.strcat fn ".checked" in
    let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
    let lax_ok =
      let uu____4088 = FStar_Options.should_verify_file fn in
      Prims.op_Negation uu____4088 in
    if lax_ok then lax_checked_file_name else checked_file_name
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4098  ->
    fun fn  ->
      match uu____4098 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4117 = FStar_Options.debug_any () in
             if uu____4117
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4124 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4124
            then
              let uu____4127 =
                let uu____4128 =
                  let uu____4129 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4129 in
                digest_of_file1 uu____4128 in
              [uu____4127]
            else [] in
          let binary_deps =
            let uu____4136 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4136
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4146 =
                      (is_interface fn1) &&
                        (let uu____4148 = lowercase_module_name fn1 in
                         uu____4148 = module_name) in
                    Prims.op_Negation uu____4146)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___122_4166 =
            match uu___122_4166 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4186 =
                    let uu____4189 = digest_of_file1 fn2 in uu____4189 :: out in
                  hash_deps uu____4186 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4195  ->
    match uu____4195 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4215 =
                  let uu____4220 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4220 FStar_Option.get in
                match uu____4215 with
                | (f_deps,uu____4242) ->
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
    let uu____4254 = FStar_Options.dep () in
    match uu____4254 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4257 = deps in
        (match uu____4257 with
         | Mk (deps1,uu____4259,uu____4260) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4265 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()