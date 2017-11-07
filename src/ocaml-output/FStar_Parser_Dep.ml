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
  fun f  -> let uu____144 = is_interface f in Prims.op_Negation uu____144
let list_of_option:
  'Auu____147 .
    'Auu____147 FStar_Pervasives_Native.option -> 'Auu____147 Prims.list
  =
  fun uu___112_155  ->
    match uu___112_155 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____161 .
    ('Auu____161 FStar_Pervasives_Native.option,'Auu____161
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____161 Prims.list
  =
  fun uu____175  ->
    match uu____175 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let module_name_of_file: Prims.string -> Prims.string =
  fun f  ->
    let uu____197 =
      let uu____200 = FStar_Util.basename f in
      check_and_strip_suffix uu____200 in
    match uu____197 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____202 =
          let uu____203 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____203 in
        FStar_Exn.raise uu____202
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____207 = module_name_of_file f in FStar_String.lowercase uu____207
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____224 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____236 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____248 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____259 . Prims.unit -> 'Auu____259 Prims.list =
  fun uu____262  -> []
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
  fun uu____351  ->
    fun k  -> match uu____351 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____380  ->
    fun k  ->
      fun v1  -> match uu____380 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____402  -> match uu____402 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____418  ->
    let uu____419 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____419
let empty_deps: deps =
  let uu____430 =
    let uu____439 = deps_empty () in
    let uu____440 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____439, uu____440, []) in
  Mk uu____430
let module_name_of_dep: dependence -> module_name =
  fun uu___113_473  ->
    match uu___113_473 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____487 = FStar_Util.smap_try_find file_system_map key in
      match uu____487 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____509) ->
          let uu____524 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____524
      | FStar_Pervasives_Native.Some
          (uu____525,FStar_Pervasives_Native.Some fn) ->
          let uu____541 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____541
      | uu____542 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____563 = FStar_Util.smap_try_find file_system_map key in
      match uu____563 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____585) ->
          FStar_Pervasives_Native.Some iface
      | uu____600 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____621 = FStar_Util.smap_try_find file_system_map key in
      match uu____621 with
      | FStar_Pervasives_Native.Some
          (uu____642,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____658 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____675 = interface_of file_system_map key in
      FStar_Option.isSome uu____675
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____684 = implementation_of file_system_map key in
      FStar_Option.isSome uu____684
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let uu____690 = FStar_Options.lax () in
    if uu____690
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
                      (let uu____717 = lowercase_module_name fn in
                       key = uu____717))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____724 = interface_of file_system_map key in
              (match uu____724 with
               | FStar_Pervasives_Native.None  ->
                   let uu____730 =
                     let uu____731 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____731 in
                   FStar_Exn.raise uu____730
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file then Prims.strcat f ".source" else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____735 =
                (cmd_line_has_impl key) &&
                  (let uu____737 = FStar_Options.dep () in
                   FStar_Option.isNone uu____737) in
              if uu____735
              then
                let uu____740 = FStar_Options.expose_interfaces () in
                (if uu____740
                 then
                   let uu____741 =
                     let uu____742 = implementation_of file_system_map key in
                     FStar_Option.get uu____742 in
                   maybe_add_suffix uu____741
                 else
                   (let uu____746 =
                      let uu____747 =
                        let uu____748 =
                          let uu____749 =
                            implementation_of file_system_map key in
                          FStar_Option.get uu____749 in
                        let uu____752 =
                          let uu____753 = interface_of file_system_map key in
                          FStar_Option.get uu____753 in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____748 uu____752 in
                      FStar_Errors.Err uu____747 in
                    FStar_Exn.raise uu____746))
              else
                (let uu____757 =
                   let uu____758 = interface_of file_system_map key in
                   FStar_Option.get uu____758 in
                 maybe_add_suffix uu____757)
          | PreferInterface key ->
              let uu____762 = implementation_of file_system_map key in
              (match uu____762 with
               | FStar_Pervasives_Native.None  ->
                   let uu____768 =
                     let uu____769 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____769 in
                   FStar_Exn.raise uu____768
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____772 = implementation_of file_system_map key in
              (match uu____772 with
               | FStar_Pervasives_Native.None  ->
                   let uu____778 =
                     let uu____779 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____779 in
                   FStar_Exn.raise uu____778
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
          let uu____809 = deps_try_find deps fn in
          match uu____809 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____823) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____854 to_1 =
          match uu____854 with
          | (d,color) ->
              let uu____874 = is_interface to_1 in
              if uu____874
              then
                let uu____881 =
                  let uu____884 =
                    let uu____885 = lowercase_module_name to_1 in
                    PreferInterface uu____885 in
                  uu____884 :: d in
                (uu____881, color)
              else
                (let uu____889 =
                   let uu____892 =
                     let uu____893 = lowercase_module_name to_1 in
                     UseImplementation uu____893 in
                   uu____892 :: d in
                 (uu____889, color)) in
        let uu____896 = deps_try_find deps from in
        match uu____896 with
        | FStar_Pervasives_Native.None  ->
            let uu____907 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____907
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____923 = add_dep key_deps to_ in
            deps_add_dep deps from uu____923
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____934 =
       let uu____935 =
         let uu____936 =
           let uu____937 =
             let uu____940 =
               let uu____943 = deps_keys graph in FStar_List.unique uu____943 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____952 =
                      let uu____957 = deps_try_find graph k in
                      FStar_Util.must uu____957 in
                    FStar_Pervasives_Native.fst uu____952 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____940 in
           FStar_String.concat "\n" uu____937 in
         Prims.strcat uu____936 "\n}\n" in
       Prims.strcat "digraph {\n" uu____935 in
     FStar_Util.write_file "dep.graph" uu____934)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____984  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____1001 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____1001 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1027 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1027
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1048 =
              let uu____1049 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____1049 in
            FStar_Exn.raise uu____1048)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1089 = FStar_Util.smap_try_find map1 key in
      match uu____1089 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1126 = is_interface full_path in
          if uu____1126
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1160 = is_interface full_path in
          if uu____1160
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1187 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1201  ->
          match uu____1201 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1187);
    FStar_List.iter
      (fun f  ->
         let uu____1212 = lowercase_module_name f in add_entry uu____1212 f)
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
        (let uu____1227 =
           let uu____1230 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1230 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1256 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1256 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1227);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1428 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1428 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1439 = string_of_lid l last1 in
      FStar_String.lowercase uu____1439
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1443 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1443
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1453 =
        let uu____1454 =
          let uu____1455 =
            let uu____1456 =
              let uu____1459 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1459 in
            FStar_Util.must uu____1456 in
          FStar_String.lowercase uu____1455 in
        uu____1454 <> k' in
      if uu____1453
      then
        let uu____1460 =
          let uu____1461 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1461 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1460
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1466 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____1480 = FStar_Options.prims_basename () in
      let uu____1481 =
        let uu____1484 = FStar_Options.pervasives_basename () in
        let uu____1485 =
          let uu____1488 = FStar_Options.pervasives_native_basename () in
          [uu____1488] in
        uu____1484 :: uu____1485 in
      uu____1480 :: uu____1481 in
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
        let uu____1899 =
          let uu____1900 =
            let uu____1901 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1901 in
          Prims.op_Negation uu____1900 in
        if uu____1899
        then
          let uu____2052 =
            let uu____2055 = FStar_ST.op_Bang deps1 in d :: uu____2055 in
          FStar_ST.op_Colon_Equals deps1 uu____2052
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true in
        let uu____2378 = resolve_module_name original_or_working_map key in
        match uu____2378 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2405 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name) in
              if uu____2405
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2428 -> false in
      let record_open_module let_open lid =
        let uu____2438 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid)) in
        if uu____2438
        then true
        else
          (if let_open
           then
             (let uu____2441 =
                let uu____2442 = string_of_lid lid true in
                FStar_Util.format1 "Module not found: %s" uu____2442 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2441)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2450 =
            let uu____2451 = string_of_lid lid true in
            FStar_Util.format1
              "No modules in namespace %s and no file with that name either"
              uu____2451 in
          FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2450
        else () in
      let record_open let_open lid =
        let uu____2460 = record_open_module let_open lid in
        if uu____2460
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2470 =
        match uu____2470 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2477 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2487 = FStar_Util.smap_try_find original_map alias in
        match uu____2487 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            FStar_Util.smap_add working_map key deps_of_aliased_module
        | FStar_Pervasives_Native.None  ->
            let uu____2539 =
              FStar_Util.format1 "module not found in search path: %s\n"
                alias in
            FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2539 in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2544 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2548 = add_dependence_edge working_map module_name in
            if uu____2548
            then ()
            else
              (let uu____2550 = FStar_Options.debug_any () in
               if uu____2550
               then
                 let uu____2551 =
                   let uu____2552 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2552 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2551
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___114_2638 =
         match uu___114_2638 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2647 =
                   let uu____2648 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2648 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2652) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2659 =
                   let uu____2660 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2660 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___115_2669 =
         match uu___115_2669 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             ((let uu____2675 =
                 let uu____2676 = lowercase_join_longident lid true in
                 PreferInterface uu____2676 in
               add_dep deps uu____2675);
              record_module_alias ident lid)
         | FStar_Parser_AST.TopLevelLet (uu____2698,patterms) ->
             FStar_List.iter
               (fun uu____2720  ->
                  match uu____2720 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2729,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2731;
               FStar_Parser_AST.mdest = uu____2732;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2734;
               FStar_Parser_AST.mdest = uu____2735;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2737,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2739;
               FStar_Parser_AST.mdest = uu____2740;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2744,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2774  -> match uu____2774 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2787,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2794 -> ()
         | FStar_Parser_AST.Pragma uu____2795 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2819 =
                 let uu____2820 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2820 > (Prims.parse_int "1") in
               if uu____2819
               then
                 let uu____2881 =
                   let uu____2882 =
                     let uu____2887 =
                       let uu____2888 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2888 in
                     (uu____2887, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2882 in
                 FStar_Exn.raise uu____2881
               else ()))
       and collect_tycon uu___116_2890 =
         match uu___116_2890 with
         | FStar_Parser_AST.TyconAbstract (uu____2891,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2903,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2917,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2963  ->
                   match uu____2963 with
                   | (uu____2972,t,uu____2974) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2979,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3038  ->
                   match uu____3038 with
                   | (uu____3051,t,uu____3053,uu____3054) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___117_3063 =
         match uu___117_3063 with
         | FStar_Parser_AST.DefineEffect (uu____3064,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3078,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___118_3089 =
         match uu___118_3089 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3090,t);
             FStar_Parser_AST.brange = uu____3092;
             FStar_Parser_AST.blevel = uu____3093;
             FStar_Parser_AST.aqual = uu____3094;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3095,t);
             FStar_Parser_AST.brange = uu____3097;
             FStar_Parser_AST.blevel = uu____3098;
             FStar_Parser_AST.aqual = uu____3099;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3101;
             FStar_Parser_AST.blevel = uu____3102;
             FStar_Parser_AST.aqual = uu____3103;_} -> collect_term t
         | uu____3104 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___119_3106 =
         match uu___119_3106 with
         | FStar_Const.Const_int
             (uu____3107,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3122 =
               let uu____3123 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3123 in
             add_dep deps uu____3122
         | FStar_Const.Const_char uu____3145 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3167 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3189 -> ()
       and collect_term' uu___120_3190 =
         match uu___120_3190 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3199 =
                   let uu____3200 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3200 in
                 collect_term' uu____3199)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3202 -> ()
         | FStar_Parser_AST.Uvar uu____3203 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3206) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3236  ->
                   match uu____3236 with | (t,uu____3242) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3252) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3254,patterms,t) ->
             (FStar_List.iter
                (fun uu____3278  ->
                   match uu____3278 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3289,t1,t2) ->
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
                (fun uu____3385  ->
                   match uu____3385 with | (uu____3390,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3393) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3449,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3452,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3455) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3461) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3467,uu____3468) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___121_3476 =
         match uu___121_3476 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3477 -> ()
         | FStar_Parser_AST.PatConst uu____3478 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3486 -> ()
         | FStar_Parser_AST.PatName uu____3493 -> ()
         | FStar_Parser_AST.PatTvar uu____3494 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3508) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3527  ->
                  match uu____3527 with | (uu____3532,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3556 =
         match uu____3556 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3574 = FStar_Parser_Driver.parse_file filename in
       match uu____3574 with
       | (ast,uu____3594) ->
           (collect_module ast;
            (let uu____3608 = FStar_ST.op_Bang deps in
             let uu____3675 = FStar_ST.op_Bang mo_roots in
             (uu____3608, uu____3675))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3771 =
        let uu____3772 = deps_try_find dep_graph file_name in
        uu____3772 = FStar_Pervasives_Native.None in
      if uu____3771
      then
        let uu____3789 = collect_one file_system_map file_name in
        match uu____3789 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3812 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3812
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3817 =
                let uu____3822 = FStar_List.unique deps1 in
                (uu____3822, White) in
              deps_add_dep dep_graph file_name uu____3817);
             (let uu____3827 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3827))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3860 =
           let uu____3865 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3865 in
         match uu____3860 with
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
                   (let uu____3884 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3884);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3890 =
                      let uu____3893 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3893 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3890))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4096 = topological_dependences_of all_cmd_line_files in
      (uu____4096, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4109  ->
    fun f  ->
      match uu____4109 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4130  ->
    fun fn  ->
      match uu____4130 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4149 = FStar_Options.debug_any () in
             if uu____4149
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4156 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4156
            then
              let uu____4159 =
                let uu____4160 =
                  let uu____4161 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4161 in
                digest_of_file1 uu____4160 in
              [uu____4159]
            else [] in
          let binary_deps =
            let uu____4168 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4168
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4178 =
                      (is_interface fn1) &&
                        (let uu____4180 = lowercase_module_name fn1 in
                         uu____4180 = module_name) in
                    Prims.op_Negation uu____4178)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___122_4198 =
            match uu___122_4198 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4218 =
                    let uu____4221 = digest_of_file1 fn2 in uu____4221 :: out in
                  hash_deps uu____4218 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4227  ->
    match uu____4227 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4247 =
                  let uu____4252 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4252 FStar_Option.get in
                match uu____4247 with
                | (f_deps,uu____4274) ->
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
  fun uu____4285  ->
    match uu____4285 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4311 =
                   let uu____4316 = deps_try_find deps f in
                   FStar_All.pipe_right uu____4316 FStar_Option.get in
                 match uu____4311 with
                 | (f_deps,uu____4338) ->
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps in
                     let files1 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files in
                     ((let uu____4348 = is_interface f in
                       if uu____4348
                       then
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" f f
                           (FStar_String.concat "\\\n\t" files1)
                       else ());
                      FStar_Util.print3 "%s.checked: %s \\\n\t%s\n\n" f f
                        (FStar_String.concat " \\\n\t" files1);
                      (let uu____4351 = is_implementation f in
                       if uu____4351
                       then
                         let ml_base_name =
                           let uu____4353 =
                             let uu____4354 =
                               let uu____4357 = FStar_Util.basename f in
                               check_and_strip_suffix uu____4357 in
                             FStar_Option.get uu____4354 in
                           FStar_Util.replace_chars uu____4353 46 "_" in
                         let uu____4358 =
                           let uu____4359 = FStar_Options.output_dir () in
                           match uu____4359 with
                           | FStar_Pervasives_Native.None  -> ""
                           | FStar_Pervasives_Native.Some x ->
                               Prims.strcat x "/" in
                         FStar_Util.print3 "%s%s.ml: %s.checked\n\n"
                           uu____4358 ml_base_name f
                       else ()))));
         (let all_fst_files =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
          let uu____4371 =
            FStar_All.pipe_right all_fst_files
              (FStar_String.concat " \\\n\t") in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n" uu____4371))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4377 = FStar_Options.dep () in
    match uu____4377 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4380 = deps in
        (match uu____4380 with
         | Mk (deps1,uu____4382,uu____4383) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4388 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()