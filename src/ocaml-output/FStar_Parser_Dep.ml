open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut[@@deriving show]
let uu___is_VerifyAll: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____5 -> false
let uu___is_VerifyUserList: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____10 -> false
let uu___is_VerifyFigureItOut: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____15 -> false
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White
  | Gray
  | Black[@@deriving show]
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____30 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____35 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____40 -> false
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____45 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____50 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____77 =
             (l > lext) &&
               (let uu____89 = FStar_String.substring f (l - lext) lext in
                uu____89 = ext) in
           if uu____77
           then
             let uu____106 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____106
           else FStar_Pervasives_Native.None) suffixes in
    let uu____118 = FStar_List.filter FStar_Util.is_some matches in
    match uu____118 with
    | (FStar_Pervasives_Native.Some m)::uu____128 ->
        FStar_Pervasives_Native.Some m
    | uu____135 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____144 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____144 = 105
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____149 = is_interface f in Prims.op_Negation uu____149
let list_of_option:
  'Auu____154 .
    'Auu____154 FStar_Pervasives_Native.option -> 'Auu____154 Prims.list
  =
  fun uu___92_162  ->
    match uu___92_162 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____170 .
    ('Auu____170 FStar_Pervasives_Native.option,'Auu____170
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____170 Prims.list
  =
  fun uu____184  ->
    match uu____184 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____207 =
      let uu____210 = FStar_Util.basename f in
      check_and_strip_suffix uu____210 in
    match uu____207 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____212 =
          let uu____213 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____213 in
        FStar_Exn.raise uu____212
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____231 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____245 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____259 -> false
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
  fun uu____370  ->
    fun k  -> match uu____370 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____402  ->
    fun k  ->
      fun v1  -> match uu____402 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____425  -> match uu____425 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____442  ->
    let uu____443 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____443
let empty_deps: deps =
  let uu____454 =
    let uu____463 = deps_empty () in
    let uu____464 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____463, uu____464, []) in
  Mk uu____454
let module_name_of_dep: dependence -> module_name =
  fun uu___93_498  ->
    match uu___93_498 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____514 = FStar_Util.smap_try_find file_system_map key in
      match uu____514 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____536) ->
          let uu____551 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____551
      | FStar_Pervasives_Native.Some
          (uu____552,FStar_Pervasives_Native.Some fn) ->
          let uu____568 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____568
      | uu____569 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____592 = FStar_Util.smap_try_find file_system_map key in
      match uu____592 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____614) ->
          FStar_Pervasives_Native.Some iface
      | uu____629 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____652 = FStar_Util.smap_try_find file_system_map key in
      match uu____652 with
      | FStar_Pervasives_Native.Some
          (uu____673,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____689 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____708 = interface_of file_system_map key in
      FStar_Option.isSome uu____708
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____719 = implementation_of file_system_map key in
      FStar_Option.isSome uu____719
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
                    (let uu____747 = lowercase_module_name fn in
                     key = uu____747))) in
        match d with
        | UseInterface key ->
            let uu____749 = interface_of file_system_map key in
            (match uu____749 with
             | FStar_Pervasives_Native.None  ->
                 let uu____752 =
                   let uu____753 =
                     FStar_Util.format1
                       "Expected an interface for module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____753 in
                 FStar_Exn.raise uu____752
             | FStar_Pervasives_Native.Some f -> f)
        | PreferInterface key when
            (let uu____758 = cmd_line_has_impl key in
             Prims.op_Negation uu____758) &&
              (has_interface file_system_map key)
            ->
            let uu____759 = interface_of file_system_map key in
            FStar_All.pipe_left FStar_Option.get uu____759
        | PreferInterface key ->
            let uu____765 = implementation_of file_system_map key in
            (match uu____765 with
             | FStar_Pervasives_Native.None  ->
                 let uu____768 =
                   let uu____769 =
                     FStar_Util.format1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____769 in
                 FStar_Exn.raise uu____768
             | FStar_Pervasives_Native.Some f -> f)
        | UseImplementation key ->
            let uu____772 = implementation_of file_system_map key in
            (match uu____772 with
             | FStar_Pervasives_Native.None  ->
                 let uu____775 =
                   let uu____776 =
                     FStar_Util.format1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStar_Errors.Err uu____776 in
                 FStar_Exn.raise uu____775
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
          let uu____802 = deps_try_find deps fn in
          match uu____802 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____816) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____850 to_1 =
          match uu____850 with
          | (d,color) ->
              let uu____870 = is_interface to_1 in
              if uu____870
              then
                let uu____877 =
                  let uu____880 =
                    let uu____881 = lowercase_module_name to_1 in
                    PreferInterface uu____881 in
                  uu____880 :: d in
                (uu____877, color)
              else
                (let uu____885 =
                   let uu____888 =
                     let uu____889 = lowercase_module_name to_1 in
                     UseImplementation uu____889 in
                   uu____888 :: d in
                 (uu____885, color)) in
        let uu____892 = deps_try_find deps from in
        match uu____892 with
        | FStar_Pervasives_Native.None  ->
            let uu____903 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____903
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____919 = add_dep key_deps to_ in
            deps_add_dep deps from uu____919
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____931 =
       let uu____932 =
         let uu____933 =
           let uu____934 =
             let uu____937 =
               let uu____940 = deps_keys graph in FStar_List.unique uu____940 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____949 =
                      let uu____954 = deps_try_find graph k in
                      FStar_Util.must uu____954 in
                    FStar_Pervasives_Native.fst uu____949 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____937 in
           FStar_String.concat "\n" uu____934 in
         Prims.strcat uu____933 "\n}\n" in
       Prims.strcat "digraph {\n" uu____932 in
     FStar_Util.write_file "dep.graph" uu____931)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____982  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____999 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____999 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1025 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1025
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1046 =
              let uu____1047 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____1047 in
            FStar_Exn.raise uu____1046)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1088 = FStar_Util.smap_try_find map1 key in
      match uu____1088 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1125 = is_interface full_path in
          if uu____1125
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1159 = is_interface full_path in
          if uu____1159
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1186 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1200  ->
          match uu____1200 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1186);
    FStar_List.iter
      (fun f  ->
         let uu____1211 = lowercase_module_name f in add_entry uu____1211 f)
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
        (let uu____1229 =
           let uu____1232 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1232 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1258 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1258 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1229);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1432 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1432 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1445 = string_of_lid l last1 in
      FStar_String.lowercase uu____1445
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1450 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1450
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1462 =
        let uu____1463 =
          let uu____1464 =
            let uu____1465 =
              let uu____1468 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1468 in
            FStar_Util.must uu____1465 in
          FStar_String.lowercase uu____1464 in
        uu____1463 <> k' in
      if uu____1462
      then
        let uu____1469 =
          let uu____1470 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1470 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1469
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1476 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1491 = FStar_Options.prims_basename () in
      let uu____1492 =
        let uu____1495 = FStar_Options.pervasives_basename () in
        let uu____1496 =
          let uu____1499 = FStar_Options.pervasives_native_basename () in
          [uu____1499] in
        uu____1495 :: uu____1496 in
      uu____1491 :: uu____1492 in
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
        let uu____1912 =
          let uu____1913 =
            let uu____1914 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1914 in
          Prims.op_Negation uu____1913 in
        if uu____1912
        then
          let uu____2065 =
            let uu____2068 = FStar_ST.op_Bang deps1 in d :: uu____2068 in
          FStar_ST.op_Colon_Equals deps1 uu____2065
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge lid =
        let key = lowercase_join_longident lid true in
        let uu____2388 = resolve_module_name working_map key in
        match uu____2388 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2415 =
                (has_interface working_map module_name) &&
                  (has_implementation working_map module_name) in
              if uu____2415
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2438 -> false in
      let record_open_module let_open lid =
        let uu____2448 = add_dependence_edge lid in
        if uu____2448
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
                (let uu____2454 =
                   let uu____2455 = string_of_lid lid true in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____2455 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2454))
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
              let uu____2471 =
                let uu____2472 = string_of_lid lid true in
                FStar_Util.format1
                  "No modules in namespace %s and no file with that name either"
                  uu____2472 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2471
        else () in
      let record_open let_open lid =
        let uu____2481 = record_open_module let_open lid in
        if uu____2481
        then ()
        else
          (let msg =
             if let_open
             then
               FStar_Pervasives_Native.Some
                 "let-open only supported for modules, not namespaces"
             else FStar_Pervasives_Native.None in
           record_open_namespace msg lid) in
      let record_open_module_or_namespace uu____2496 =
        match uu____2496 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  ->
                 record_open_namespace FStar_Pervasives_Native.None lid
             | Open_module  ->
                 let uu____2503 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2513 = FStar_Util.smap_try_find original_map alias in
        match uu____2513 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2565 =
              let uu____2566 =
                let uu____2571 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias in
                (uu____2571, (FStar_Ident.range_of_lid lid)) in
              FStar_Errors.Error uu____2566 in
            FStar_Exn.raise uu____2565 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2576 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2580 = add_dependence_edge module_name in
            if uu____2580
            then ()
            else
              (let uu____2582 = FStar_Options.debug_any () in
               if uu____2582
               then
                 let uu____2583 =
                   let uu____2584 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2584 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2583
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___94_2670 =
         match uu___94_2670 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2679 =
                   let uu____2680 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2680 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2684) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2691 =
                   let uu____2692 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2692 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___95_2701 =
         match uu___95_2701 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2707 =
                 let uu____2708 = lowercase_join_longident lid true in
                 PreferInterface uu____2708 in
               add_dep deps uu____2707);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2730,patterms) ->
             FStar_List.iter
               (fun uu____2752  ->
                  match uu____2752 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2761,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2763;
               FStar_Parser_AST.mdest = uu____2764;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2766;
               FStar_Parser_AST.mdest = uu____2767;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2769,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2771;
               FStar_Parser_AST.mdest = uu____2772;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2776,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2806  -> match uu____2806 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2819,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2826 -> ()
         | FStar_Parser_AST.Pragma uu____2827 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2851 =
                 let uu____2852 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2852 > (Prims.parse_int "1") in
               if uu____2851
               then
                 let uu____2913 =
                   let uu____2914 =
                     let uu____2919 =
                       let uu____2920 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2920 in
                     (uu____2919, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2914 in
                 FStar_Exn.raise uu____2913
               else ()))
       and collect_tycon uu___96_2922 =
         match uu___96_2922 with
         | FStar_Parser_AST.TyconAbstract (uu____2923,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2935,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2949,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2995  ->
                   match uu____2995 with
                   | (uu____3004,t,uu____3006) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3011,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3070  ->
                   match uu____3070 with
                   | (uu____3083,t,uu____3085,uu____3086) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___97_3095 =
         match uu___97_3095 with
         | FStar_Parser_AST.DefineEffect (uu____3096,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3110,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___98_3121 =
         match uu___98_3121 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3122,t);
             FStar_Parser_AST.brange = uu____3124;
             FStar_Parser_AST.blevel = uu____3125;
             FStar_Parser_AST.aqual = uu____3126;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3127,t);
             FStar_Parser_AST.brange = uu____3129;
             FStar_Parser_AST.blevel = uu____3130;
             FStar_Parser_AST.aqual = uu____3131;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3133;
             FStar_Parser_AST.blevel = uu____3134;
             FStar_Parser_AST.aqual = uu____3135;_} -> collect_term t
         | uu____3136 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___99_3138 =
         match uu___99_3138 with
         | FStar_Const.Const_int
             (uu____3139,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3154 =
               let uu____3155 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3155 in
             add_dep deps uu____3154
         | FStar_Const.Const_char uu____3177 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3199 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3221 -> ()
       and collect_term' uu___100_3222 =
         match uu___100_3222 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3231 =
                   let uu____3232 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3232 in
                 collect_term' uu____3231)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3234 -> ()
         | FStar_Parser_AST.Uvar uu____3235 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3238) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3268  ->
                   match uu____3268 with | (t,uu____3274) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3284) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3286,patterms,t) ->
             (FStar_List.iter
                (fun uu____3310  ->
                   match uu____3310 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3321,t1,t2) ->
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
                (fun uu____3417  ->
                   match uu____3417 with | (uu____3422,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3425) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3481,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3484,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3487) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3493) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3499,uu____3500) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___101_3508 =
         match uu___101_3508 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3509 -> ()
         | FStar_Parser_AST.PatConst uu____3510 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3518 -> ()
         | FStar_Parser_AST.PatName uu____3525 -> ()
         | FStar_Parser_AST.PatTvar uu____3526 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3540) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3559  ->
                  match uu____3559 with | (uu____3564,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3588 =
         match uu____3588 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3606 = FStar_Parser_Driver.parse_file filename in
       match uu____3606 with
       | (ast,uu____3626) ->
           (collect_module ast;
            (let uu____3640 = FStar_ST.op_Bang deps in
             let uu____3707 = FStar_ST.op_Bang mo_roots in
             (uu____3640, uu____3707))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3804 =
        let uu____3805 = deps_try_find dep_graph file_name in
        uu____3805 = FStar_Pervasives_Native.None in
      if uu____3804
      then
        let uu____3822 = collect_one file_system_map file_name in
        match uu____3822 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3845 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3845
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3850 =
                let uu____3855 = FStar_List.unique deps1 in
                (uu____3855, White) in
              deps_add_dep dep_graph file_name uu____3850);
             (let uu____3860 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3860))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3893 =
           let uu____3898 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3898 in
         match uu____3893 with
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
                   (let uu____3917 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3917);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3923 =
                      let uu____3926 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3926 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3923))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4129 = topological_dependences_of all_cmd_line_files in
      (uu____4129, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4144  ->
    fun f  ->
      match uu____4144 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let checked_file_name = Prims.strcat fn ".checked" in
    let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
    let lax_ok =
      let uu____4164 = FStar_Options.should_verify_file fn in
      Prims.op_Negation uu____4164 in
    if lax_ok then lax_checked_file_name else checked_file_name
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4176  ->
    fun fn  ->
      match uu____4176 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4195 = FStar_Options.debug_any () in
             if uu____4195
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4202 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4202
            then
              let uu____4205 =
                let uu____4206 =
                  let uu____4207 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4207 in
                digest_of_file1 uu____4206 in
              [uu____4205]
            else [] in
          let binary_deps =
            let uu____4214 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4214
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4224 =
                      (is_interface fn1) &&
                        (let uu____4226 = lowercase_module_name fn1 in
                         uu____4226 = module_name) in
                    Prims.op_Negation uu____4224)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___102_4244 =
            match uu___102_4244 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4264 =
                    let uu____4267 = digest_of_file1 fn2 in uu____4267 :: out in
                  hash_deps uu____4264 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4274  ->
    match uu____4274 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4294 =
                  let uu____4299 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4299 FStar_Option.get in
                match uu____4294 with
                | (f_deps,uu____4321) ->
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
    let uu____4334 = FStar_Options.dep () in
    match uu____4334 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4337 = deps in
        (match uu____4337 with
         | Mk (deps1,uu____4339,uu____4340) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4345 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()