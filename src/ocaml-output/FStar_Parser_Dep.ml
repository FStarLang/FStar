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
  fun uu___111_162  ->
    match uu___111_162 with
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
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____227 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____241 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____254 . Prims.unit -> 'Auu____254 Prims.list =
  fun uu____257  -> []
type dependence_graph =
  | Deps of (dependences,color) FStar_Pervasives_Native.tuple2
  FStar_Util.smap[@@deriving show]
let uu___is_Deps: dependence_graph -> Prims.bool = fun projectee  -> true
let __proj__Deps__item___0:
  dependence_graph ->
    (dependences,color) FStar_Pervasives_Native.tuple2 FStar_Util.smap
  = fun projectee  -> match projectee with | Deps _0 -> _0
type deps =
  | Mk of (dependence_graph,files_for_module_name)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Mk: deps -> Prims.bool = fun projectee  -> true
let __proj__Mk__item___0:
  deps ->
    (dependence_graph,files_for_module_name) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Mk _0 -> _0
let deps_try_find:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun uu____336  ->
    fun k  -> match uu____336 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____368  ->
    fun k  ->
      fun v1  -> match uu____368 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____391  -> match uu____391 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____408  ->
    let uu____409 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____409
let module_name_of_dep: dependence -> module_name =
  fun uu___112_423  ->
    match uu___112_423 with
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____438 = FStar_Util.smap_try_find file_system_map key in
      match uu____438 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____460) ->
          let uu____475 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____475
      | FStar_Pervasives_Native.Some
          (uu____476,FStar_Pervasives_Native.Some fn) ->
          let uu____492 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____492
      | uu____493 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____516 = FStar_Util.smap_try_find file_system_map key in
      match uu____516 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____538) ->
          FStar_Pervasives_Native.Some iface
      | uu____553 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____576 = FStar_Util.smap_try_find file_system_map key in
      match uu____576 with
      | FStar_Pervasives_Native.Some
          (uu____597,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____613 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____632 = interface_of file_system_map key in
      FStar_Option.isSome uu____632
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____643 = implementation_of file_system_map key in
      FStar_Option.isSome uu____643
let file_of_dep: files_for_module_name -> dependence -> file_name =
  fun file_system_map  ->
    fun d  ->
      match d with
      | PreferInterface key when has_interface file_system_map key ->
          let uu____655 = interface_of file_system_map key in
          FStar_All.pipe_left FStar_Option.get uu____655
      | PreferInterface key ->
          let uu____661 = implementation_of file_system_map key in
          (match uu____661 with
           | FStar_Pervasives_Native.None  ->
               let uu____664 =
                 let uu____665 =
                   FStar_Util.format1
                     "Expected an implementation of module %s, but couldn't find one"
                     key in
                 FStar_Errors.Err uu____665 in
               FStar_Exn.raise uu____664
           | FStar_Pervasives_Native.Some f -> f)
      | UseImplementation key ->
          let uu____668 = implementation_of file_system_map key in
          (match uu____668 with
           | FStar_Pervasives_Native.None  ->
               let uu____671 =
                 let uu____672 =
                   FStar_Util.format1
                     "Expected an implementation of module %s, but couldn't find one"
                     key in
                 FStar_Errors.Err uu____672 in
               FStar_Exn.raise uu____671
           | FStar_Pervasives_Native.Some f -> f)
let dependences_of:
  files_for_module_name ->
    dependence_graph -> file_name -> file_name Prims.list
  =
  fun file_system_map  ->
    fun deps  ->
      fun fn  ->
        let uu____690 = deps_try_find deps fn in
        match uu____690 with
        | FStar_Pervasives_Native.None  -> empty_dependences ()
        | FStar_Pervasives_Native.Some (deps1,uu____704) ->
            FStar_List.map (file_of_dep file_system_map) deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____738 to_1 =
          match uu____738 with
          | (d,color) ->
              let uu____758 = is_interface to_1 in
              if uu____758
              then
                let uu____765 =
                  let uu____768 =
                    let uu____769 = lowercase_module_name to_1 in
                    PreferInterface uu____769 in
                  uu____768 :: d in
                (uu____765, color)
              else
                (let uu____773 =
                   let uu____776 =
                     let uu____777 = lowercase_module_name to_1 in
                     UseImplementation uu____777 in
                   uu____776 :: d in
                 (uu____773, color)) in
        let uu____780 = deps_try_find deps from in
        match uu____780 with
        | FStar_Pervasives_Native.None  ->
            let uu____791 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____791
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____807 = add_dep key_deps to_ in
            deps_add_dep deps from uu____807
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____819 =
       let uu____820 =
         let uu____821 =
           let uu____822 =
             let uu____825 =
               let uu____828 = deps_keys graph in FStar_List.unique uu____828 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____837 =
                      let uu____842 = deps_try_find graph k in
                      FStar_Util.must uu____842 in
                    FStar_Pervasives_Native.fst uu____837 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____825 in
           FStar_String.concat "\n" uu____822 in
         Prims.strcat uu____821 "\n}\n" in
       Prims.strcat "digraph {\n" uu____820 in
     FStar_Util.write_file "dep.graph" uu____819)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____870  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____887 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____887 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____913 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____913
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____934 =
              let uu____935 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____935 in
            FStar_Exn.raise uu____934)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____976 = FStar_Util.smap_try_find map1 key in
      match uu____976 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1013 = is_interface full_path in
          if uu____1013
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1047 = is_interface full_path in
          if uu____1047
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1074 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1088  ->
          match uu____1088 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1074);
    FStar_List.iter
      (fun f  ->
         let uu____1099 = lowercase_module_name f in add_entry uu____1099 f)
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
        (let uu____1117 =
           let uu____1120 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1120 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1146 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1146 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1117);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1320 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1320 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1333 = string_of_lid l last1 in
      FStar_String.lowercase uu____1333
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1338 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1338
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1350 =
        let uu____1351 =
          let uu____1352 =
            let uu____1353 =
              let uu____1356 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1356 in
            FStar_Util.must uu____1353 in
          FStar_String.lowercase uu____1352 in
        uu____1351 <> k' in
      if uu____1350
      then
        let uu____1357 =
          let uu____1358 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
            uu____1358 filename in
        FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____1357
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1364 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1379 = FStar_Options.prims_basename () in
      let uu____1380 =
        let uu____1383 = FStar_Options.pervasives_basename () in
        let uu____1384 =
          let uu____1387 = FStar_Options.pervasives_native_basename () in
          [uu____1387] in
        uu____1383 :: uu____1384 in
      uu____1379 :: uu____1380 in
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
        let uu____1800 =
          let uu____1801 =
            let uu____1802 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1802 in
          Prims.op_Negation uu____1801 in
        if uu____1800
        then
          let uu____1953 =
            let uu____1956 = FStar_ST.op_Bang deps1 in d :: uu____1956 in
          FStar_ST.op_Colon_Equals deps1 uu____1953
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge lid =
        let key = lowercase_join_longident lid true in
        let uu____2276 = resolve_module_name working_map key in
        match uu____2276 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2303 =
                (has_interface working_map module_name) &&
                  (has_implementation working_map module_name) in
              if uu____2303
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2326 -> false in
      let record_open_module let_open lid =
        let uu____2336 = add_dependence_edge lid in
        if uu____2336
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
                (let uu____2342 =
                   let uu____2343 = string_of_lid lid true in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____2343 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2342))
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
              let uu____2359 =
                let uu____2360 = string_of_lid lid true in
                FStar_Util.format1
                  "No modules in namespace %s and no file with that name either"
                  uu____2360 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2359
        else () in
      let record_open let_open lid =
        let uu____2369 = record_open_module let_open lid in
        if uu____2369
        then ()
        else
          (let msg =
             if let_open
             then
               FStar_Pervasives_Native.Some
                 "let-open only supported for modules, not namespaces"
             else FStar_Pervasives_Native.None in
           record_open_namespace msg lid) in
      let record_open_module_or_namespace uu____2384 =
        match uu____2384 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  ->
                 record_open_namespace FStar_Pervasives_Native.None lid
             | Open_module  ->
                 let uu____2391 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2401 = FStar_Util.smap_try_find original_map alias in
        match uu____2401 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2453 =
              let uu____2454 =
                let uu____2459 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias in
                (uu____2459, (FStar_Ident.range_of_lid lid)) in
              FStar_Errors.Error uu____2454 in
            FStar_Exn.raise uu____2453 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2464 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2468 = add_dependence_edge module_name in
            if uu____2468
            then ()
            else
              (let uu____2470 = FStar_Options.debug_any () in
               if uu____2470
               then
                 let uu____2471 =
                   let uu____2472 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2472 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2471
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___113_2558 =
         match uu___113_2558 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2567 =
                   let uu____2568 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2568 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2572) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2579 =
                   let uu____2580 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2580 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___114_2589 =
         match uu___114_2589 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2595 =
                 let uu____2596 = lowercase_join_longident lid true in
                 PreferInterface uu____2596 in
               add_dep deps uu____2595);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2618,patterms) ->
             FStar_List.iter
               (fun uu____2640  ->
                  match uu____2640 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2649,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2651;
               FStar_Parser_AST.mdest = uu____2652;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2654;
               FStar_Parser_AST.mdest = uu____2655;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2657,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2659;
               FStar_Parser_AST.mdest = uu____2660;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2664,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2694  -> match uu____2694 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2707,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2714 -> ()
         | FStar_Parser_AST.Pragma uu____2715 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2739 =
                 let uu____2740 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2740 > (Prims.parse_int "1") in
               if uu____2739
               then
                 let uu____2801 =
                   let uu____2802 =
                     let uu____2807 =
                       let uu____2808 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2808 in
                     (uu____2807, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2802 in
                 FStar_Exn.raise uu____2801
               else ()))
       and collect_tycon uu___115_2810 =
         match uu___115_2810 with
         | FStar_Parser_AST.TyconAbstract (uu____2811,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2823,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2837,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2883  ->
                   match uu____2883 with
                   | (uu____2892,t,uu____2894) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2899,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2958  ->
                   match uu____2958 with
                   | (uu____2971,t,uu____2973,uu____2974) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___116_2983 =
         match uu___116_2983 with
         | FStar_Parser_AST.DefineEffect (uu____2984,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2998,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___117_3009 =
         match uu___117_3009 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3010,t);
             FStar_Parser_AST.brange = uu____3012;
             FStar_Parser_AST.blevel = uu____3013;
             FStar_Parser_AST.aqual = uu____3014;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3015,t);
             FStar_Parser_AST.brange = uu____3017;
             FStar_Parser_AST.blevel = uu____3018;
             FStar_Parser_AST.aqual = uu____3019;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3021;
             FStar_Parser_AST.blevel = uu____3022;
             FStar_Parser_AST.aqual = uu____3023;_} -> collect_term t
         | uu____3024 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___118_3026 =
         match uu___118_3026 with
         | FStar_Const.Const_int
             (uu____3027,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3042 =
               let uu____3043 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3043 in
             add_dep deps uu____3042
         | FStar_Const.Const_char uu____3065 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3087 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3109 -> ()
       and collect_term' uu___119_3110 =
         match uu___119_3110 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3119 =
                   let uu____3120 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3120 in
                 collect_term' uu____3119)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3122 -> ()
         | FStar_Parser_AST.Uvar uu____3123 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3126) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3156  ->
                   match uu____3156 with | (t,uu____3162) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3172) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3174,patterms,t) ->
             (FStar_List.iter
                (fun uu____3198  ->
                   match uu____3198 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3209,t1,t2) ->
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
                (fun uu____3305  ->
                   match uu____3305 with | (uu____3310,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3313) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3369,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3372,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3375) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3381) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3387,uu____3388) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___120_3396 =
         match uu___120_3396 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3397 -> ()
         | FStar_Parser_AST.PatConst uu____3398 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3406 -> ()
         | FStar_Parser_AST.PatName uu____3413 -> ()
         | FStar_Parser_AST.PatTvar uu____3414 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3428) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3447  ->
                  match uu____3447 with | (uu____3452,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3476 =
         match uu____3476 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3494 = FStar_Parser_Driver.parse_file filename in
       match uu____3494 with
       | (ast,uu____3514) ->
           (collect_module ast;
            (let uu____3528 = FStar_ST.op_Bang deps in
             let uu____3595 = FStar_ST.op_Bang mo_roots in
             (uu____3528, uu____3595))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun filenames  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map filenames in
    let rec discover_one file_name =
      let uu____3692 =
        let uu____3693 = deps_try_find dep_graph file_name in
        uu____3693 = FStar_Pervasives_Native.None in
      if uu____3692
      then
        let uu____3710 = collect_one file_system_map file_name in
        match uu____3710 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3733 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3733
              then FStar_List.append deps [PreferInterface module_name]
              else deps in
            ((let uu____3738 =
                let uu____3743 = FStar_List.unique deps1 in
                (uu____3743, White) in
              deps_add_dep dep_graph file_name uu____3738);
             (let uu____3748 =
                FStar_List.map (file_of_dep file_system_map)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3748))
      else () in
    FStar_List.iter discover_one filenames;
    (let uu____3753 =
       let uu____3754 = FStar_List.hd filenames in
       let uu____3755 = FStar_List.tl filenames in
       FStar_List.fold_left
         (fun previous_file  ->
            fun file  -> add_dependence dep_graph file previous_file; file)
         uu____3754 uu____3755 in
     let topological_dependences_of filename =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename1 =
         let uu____3788 =
           let uu____3793 = deps_try_find dep_graph filename1 in
           FStar_Util.must uu____3793 in
         match uu____3788 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1_warning
                     "Recursive dependency on module %s\n" filename1;
                   FStar_Util.print1
                     "The cycle contains a subset of the modules in:\n%s \n"
                     (FStar_String.concat "\n`used by` " cycle);
                   print_graph dep_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename1 (direct_deps, Gray);
                   (let uu____3812 =
                      dependences_of file_system_map dep_graph filename1 in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3812);
                   deps_add_dep dep_graph filename1 (direct_deps, Black);
                   (let uu____3818 =
                      let uu____3821 = FStar_ST.op_Bang topologically_sorted in
                      filename1 :: uu____3821 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3818))) in
       aux [] filename; FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right filenames
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4024 =
        let uu____4027 =
          let uu____4028 = FStar_List.last filenames in
          FStar_Option.get uu____4028 in
        topological_dependences_of uu____4027 in
      (uu____4024, (Mk (dep_graph, file_system_map)))))
let print_make: deps -> Prims.unit =
  fun uu____4036  ->
    match uu____4036 with
    | Mk (deps,file_system_map) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4051 =
                  let uu____4056 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4056 FStar_Option.get in
                match uu____4051 with
                | (f_deps,uu____4078) ->
                    let files =
                      FStar_List.map (file_of_dep file_system_map) f_deps in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files in
                    FStar_Util.print2 "%s: %s\n" f
                      (FStar_String.concat " " files1)))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4091 = FStar_Options.dep () in
    match uu____4091 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4094 = deps in
        (match uu____4094 with | Mk (deps1,uu____4096) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4097 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()