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
  fun uu___64_152  ->
    match uu___64_152 with
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
          let uu____200 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____200 in
        FStar_Exn.raise uu____199
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____204 = module_name_of_file f in FStar_String.lowercase uu____204
let namespace_of_module:
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun f  ->
    let lid =
      FStar_Ident.lid_of_path (FStar_Ident.path_of_text f)
        FStar_Range.dummyRange in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____213 ->
        let uu____216 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
        FStar_Pervasives_Native.Some uu____216
type file_name = Prims.string[@@deriving show]
type module_name = Prims.string[@@deriving show]
type dependence =
  | UseInterface of module_name
  | PreferInterface of module_name
  | UseImplementation of module_name[@@deriving show]
let uu___is_UseInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____233 -> false
let __proj__UseInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____245 -> false
let __proj__PreferInterface__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation: dependence -> Prims.bool =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____257 -> false
let __proj__UseImplementation__item___0: dependence -> module_name =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0
type dependences = dependence Prims.list[@@deriving show]
let empty_dependences: 'Auu____268 . Prims.unit -> 'Auu____268 Prims.list =
  fun uu____271  -> []
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
  fun uu____360  ->
    fun k  -> match uu____360 with | Deps m -> FStar_Util.smap_try_find m k
let deps_add_dep:
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____389  ->
    fun k  ->
      fun v1  -> match uu____389 with | Deps m -> FStar_Util.smap_add m k v1
let deps_keys: dependence_graph -> Prims.string Prims.list =
  fun uu____411  -> match uu____411 with | Deps m -> FStar_Util.smap_keys m
let deps_empty: Prims.unit -> dependence_graph =
  fun uu____427  ->
    let uu____428 = FStar_Util.smap_create (Prims.parse_int "41") in
    Deps uu____428
let empty_deps: deps =
  let uu____439 =
    let uu____448 = deps_empty () in
    let uu____449 = FStar_Util.smap_create (Prims.parse_int "0") in
    (uu____448, uu____449, []) in
  Mk uu____439
let module_name_of_dep: dependence -> module_name =
  fun uu___65_482  ->
    match uu___65_482 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
let resolve_module_name:
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____496 = FStar_Util.smap_try_find file_system_map key in
      match uu____496 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____518) ->
          let uu____533 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____533
      | FStar_Pervasives_Native.Some
          (uu____534,FStar_Pervasives_Native.Some fn) ->
          let uu____550 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu____550
      | uu____551 -> FStar_Pervasives_Native.None
let interface_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____572 = FStar_Util.smap_try_find file_system_map key in
      match uu____572 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____594) ->
          FStar_Pervasives_Native.Some iface
      | uu____609 -> FStar_Pervasives_Native.None
let implementation_of:
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option
  =
  fun file_system_map  ->
    fun key  ->
      let uu____630 = FStar_Util.smap_try_find file_system_map key in
      match uu____630 with
      | FStar_Pervasives_Native.Some
          (uu____651,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____667 -> FStar_Pervasives_Native.None
let has_interface: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____684 = interface_of file_system_map key in
      FStar_Option.isSome uu____684
let has_implementation: files_for_module_name -> module_name -> Prims.bool =
  fun file_system_map  ->
    fun key  ->
      let uu____693 = implementation_of file_system_map key in
      FStar_Option.isSome uu____693
let cache_file_name: Prims.string -> Prims.string =
  fun fn  ->
    let uu____699 = FStar_Options.lax () in
    if uu____699
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
                      (let uu____726 = lowercase_module_name fn in
                       key = uu____726))) in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu____733 = interface_of file_system_map key in
              (match uu____733 with
               | FStar_Pervasives_Native.None  ->
                   let uu____739 =
                     let uu____740 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____740 in
                   FStar_Exn.raise uu____739
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file then Prims.strcat f ".source" else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____744 =
                (cmd_line_has_impl key) &&
                  (let uu____746 = FStar_Options.dep () in
                   FStar_Option.isNone uu____746) in
              if uu____744
              then
                let uu____749 = FStar_Options.expose_interfaces () in
                (if uu____749
                 then
                   let uu____750 =
                     let uu____751 = implementation_of file_system_map key in
                     FStar_Option.get uu____751 in
                   maybe_add_suffix uu____750
                 else
                   (let uu____755 =
                      let uu____756 =
                        let uu____757 =
                          let uu____758 =
                            implementation_of file_system_map key in
                          FStar_Option.get uu____758 in
                        let uu____761 =
                          let uu____762 = interface_of file_system_map key in
                          FStar_Option.get uu____762 in
                        FStar_Util.format2
                          "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          uu____757 uu____761 in
                      FStar_Errors.Err uu____756 in
                    FStar_Exn.raise uu____755))
              else
                (let uu____766 =
                   let uu____767 = interface_of file_system_map key in
                   FStar_Option.get uu____767 in
                 maybe_add_suffix uu____766)
          | PreferInterface key ->
              let uu____771 = implementation_of file_system_map key in
              (match uu____771 with
               | FStar_Pervasives_Native.None  ->
                   let uu____777 =
                     let uu____778 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____778 in
                   FStar_Exn.raise uu____777
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____781 = implementation_of file_system_map key in
              (match uu____781 with
               | FStar_Pervasives_Native.None  ->
                   let uu____787 =
                     let uu____788 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key in
                     FStar_Errors.Err uu____788 in
                   FStar_Exn.raise uu____787
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
          let uu____818 = deps_try_find deps fn in
          match uu____818 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____832) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
let add_dependence: dependence_graph -> file_name -> file_name -> Prims.unit
  =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____863 to_1 =
          match uu____863 with
          | (d,color) ->
              let uu____883 = is_interface to_1 in
              if uu____883
              then
                let uu____890 =
                  let uu____893 =
                    let uu____894 = lowercase_module_name to_1 in
                    PreferInterface uu____894 in
                  uu____893 :: d in
                (uu____890, color)
              else
                (let uu____898 =
                   let uu____901 =
                     let uu____902 = lowercase_module_name to_1 in
                     UseImplementation uu____902 in
                   uu____901 :: d in
                 (uu____898, color)) in
        let uu____905 = deps_try_find deps from in
        match uu____905 with
        | FStar_Pervasives_Native.None  ->
            let uu____916 = add_dep ((empty_dependences ()), White) to_ in
            deps_add_dep deps from uu____916
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____932 = add_dep key_deps to_ in
            deps_add_dep deps from uu____932
let print_graph: dependence_graph -> Prims.unit =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____943 =
       let uu____944 =
         let uu____945 =
           let uu____946 =
             let uu____949 =
               let uu____952 = deps_keys graph in FStar_List.unique uu____952 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____961 =
                      let uu____966 = deps_try_find graph k in
                      FStar_Util.must uu____966 in
                    FStar_Pervasives_Native.fst uu____961 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  let print7 dep1 =
                    FStar_Util.format2 " %s -> %s" (r k)
                      (r (module_name_of_dep dep1)) in
                  FStar_List.map print7 deps) uu____949 in
           FStar_String.concat "\n" uu____946 in
         Prims.strcat uu____945 "\n}\n" in
       Prims.strcat "digraph {\n" uu____944 in
     FStar_Util.write_file "dep.graph" uu____943)
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____995  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____1012 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____1012 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____1038 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____1038
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____1059 =
              let uu____1060 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____1060 in
            FStar_Exn.raise uu____1059)) include_directories2
let build_map: Prims.string Prims.list -> files_for_module_name =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____1100 = FStar_Util.smap_try_find map1 key in
      match uu____1100 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1137 = is_interface full_path in
          if uu____1137
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1171 = is_interface full_path in
          if uu____1171
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____1198 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____1212  ->
          match uu____1212 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1198);
    FStar_List.iter
      (fun f  ->
         let uu____1223 = lowercase_module_name f in add_entry uu____1223 f)
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
        (let uu____1238 =
           let uu____1241 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____1241 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____1267 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____1267 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1238);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____1439 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____1439 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____1450 = string_of_lid l last1 in
      FStar_String.lowercase uu____1450
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____1454 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____1454
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____1464 =
        let uu____1465 =
          let uu____1466 =
            let uu____1467 =
              let uu____1470 = FStar_Util.basename filename in
              check_and_strip_suffix uu____1470 in
            FStar_Util.must uu____1467 in
          FStar_String.lowercase uu____1466 in
        uu____1465 <> k' in
      if uu____1464
      then
        let uu____1471 =
          let uu____1472 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
            uu____1472 filename in
        FStar_Errors.err (FStar_Ident.range_of_lid lid) uu____1471
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1477 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename in
    let corelibs =
      let uu____1491 = FStar_Options.prims_basename () in
      let uu____1492 =
        let uu____1495 = FStar_Options.pervasives_basename () in
        let uu____1496 =
          let uu____1499 = FStar_Options.pervasives_native_basename () in
          [uu____1499] in
        uu____1495 :: uu____1496 in
      uu____1491 :: uu____1492 in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)] in
       let uu____1534 =
         let uu____1537 = lowercase_module_name full_filename in
         namespace_of_module uu____1537 in
       match uu____1534 with
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
        let uu____1940 =
          let uu____1941 =
            let uu____1942 = FStar_ST.op_Bang deps1 in
            FStar_List.existsML (fun d'  -> d' = d) uu____1942 in
          Prims.op_Negation uu____1941 in
        if uu____1940
        then
          let uu____2093 =
            let uu____2096 = FStar_ST.op_Bang deps1 in d :: uu____2096 in
          FStar_ST.op_Colon_Equals deps1 uu____2093
        else () in
      let working_map = FStar_Util.smap_copy original_map in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true in
        let uu____2419 = resolve_module_name original_or_working_map key in
        match uu____2419 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2446 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name) in
              if uu____2446
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2469 -> false in
      let record_open_module let_open lid =
        let uu____2479 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid)) in
        if uu____2479
        then true
        else
          (if let_open
           then
             (let uu____2482 =
                let uu____2483 = string_of_lid lid true in
                FStar_Util.format1 "Module not found: %s" uu____2483 in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2482)
           else ();
           false) in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true in
        let r = enter_namespace original_map working_map key in
        if Prims.op_Negation r
        then
          let uu____2491 =
            let uu____2492 = string_of_lid lid true in
            FStar_Util.format1
              "No modules in namespace %s and no file with that name either"
              uu____2492 in
          FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2491
        else () in
      let record_open let_open lid =
        let uu____2501 = record_open_module let_open lid in
        if uu____2501
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else () in
      let record_open_module_or_namespace uu____2511 =
        match uu____2511 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2518 = record_open_module false lid in ()) in
      let record_module_alias ident lid =
        let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
        let alias = lowercase_join_longident lid true in
        let uu____2528 = FStar_Util.smap_try_find original_map alias in
        match uu____2528 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2582 =
                FStar_Util.format1 "module not found in search path: %s\n"
                  alias in
              FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2582);
             false) in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2587 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
            let uu____2591 = add_dependence_edge working_map module_name in
            if uu____2591
            then ()
            else
              (let uu____2593 = FStar_Options.debug_any () in
               if uu____2593
               then
                 let uu____2594 =
                   let uu____2595 = FStar_Ident.string_of_lid module_name in
                   FStar_Util.format1 "Unbound module reference %s"
                     uu____2595 in
                 FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____2594
               else ()) in
      let auto_open = hard_coded_dependencies filename in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0") in
       let rec collect_module uu___66_2681 =
         match uu___66_2681 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2690 =
                   let uu____2691 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2691 in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2695) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2702 =
                   let uu____2703 = namespace_of_lid lid in
                   enter_namespace original_map working_map uu____2703 in
                 ())
              else ();
              collect_decls decls)
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       and collect_decl uu___67_2712 =
         match uu___67_2712 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2717 = record_module_alias ident lid in
             if uu____2717
             then
               let uu____2718 =
                 let uu____2719 = lowercase_join_longident lid true in
                 PreferInterface uu____2719 in
               add_dep deps uu____2718
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2742,patterms) ->
             FStar_List.iter
               (fun uu____2764  ->
                  match uu____2764 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Assume (uu____2773,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2775;
               FStar_Parser_AST.mdest = uu____2776;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2778;
               FStar_Parser_AST.mdest = uu____2779;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2781,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2783;
               FStar_Parser_AST.mdest = uu____2784;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2788,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2818  -> match uu____2818 with | (x,docnik) -> x)
                 ts in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2831,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2838 -> ()
         | FStar_Parser_AST.Pragma uu____2839 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2863 =
                 let uu____2864 = FStar_ST.op_Bang num_of_toplevelmods in
                 uu____2864 > (Prims.parse_int "1") in
               if uu____2863
               then
                 let uu____2925 =
                   let uu____2926 =
                     let uu____2931 =
                       let uu____2932 = string_of_lid lid true in
                       FStar_Util.format1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu____2932 in
                     (uu____2931, (FStar_Ident.range_of_lid lid)) in
                   FStar_Errors.Error uu____2926 in
                 FStar_Exn.raise uu____2925
               else ()))
       and collect_tycon uu___68_2934 =
         match uu___68_2934 with
         | FStar_Parser_AST.TyconAbstract (uu____2935,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2947,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2961,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3007  ->
                   match uu____3007 with
                   | (uu____3016,t,uu____3018) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____3023,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____3082  ->
                   match uu____3082 with
                   | (uu____3095,t,uu____3097,uu____3098) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       and collect_effect_decl uu___69_3107 =
         match uu___69_3107 with
         | FStar_Parser_AST.DefineEffect (uu____3108,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____3122,binders,t) ->
             (collect_binders binders; collect_term t)
       and collect_binders binders = FStar_List.iter collect_binder binders
       and collect_binder uu___70_3133 =
         match uu___70_3133 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3134,t);
             FStar_Parser_AST.brange = uu____3136;
             FStar_Parser_AST.blevel = uu____3137;
             FStar_Parser_AST.aqual = uu____3138;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3139,t);
             FStar_Parser_AST.brange = uu____3141;
             FStar_Parser_AST.blevel = uu____3142;
             FStar_Parser_AST.aqual = uu____3143;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____3145;
             FStar_Parser_AST.blevel = uu____3146;
             FStar_Parser_AST.aqual = uu____3147;_} -> collect_term t
         | uu____3148 -> ()
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       and collect_constant uu___71_3150 =
         match uu___71_3150 with
         | FStar_Const.Const_int
             (uu____3151,FStar_Pervasives_Native.Some (signedness,width)) ->
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
             let uu____3166 =
               let uu____3167 = FStar_Util.format2 "fstar.%sint%s" u w in
               PreferInterface uu____3167 in
             add_dep deps uu____3166
         | FStar_Const.Const_char uu____3189 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3211 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3233 -> ()
       and collect_term' uu___72_3234 =
         match uu___72_3234 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             (if (FStar_Ident.text_of_id s) = "@"
              then
                (let uu____3243 =
                   let uu____3244 =
                     FStar_Ident.lid_of_path
                       (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
                       FStar_Range.dummyRange in
                   FStar_Parser_AST.Name uu____3244 in
                 collect_term' uu____3243)
              else ();
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3246 -> ()
         | FStar_Parser_AST.Uvar uu____3247 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3250) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3280  ->
                   match uu____3280 with | (t,uu____3286) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3296) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3298,patterms,t) ->
             (FStar_List.iter
                (fun uu____3322  ->
                   match uu____3322 with
                   | (pat,t1) -> (collect_pattern pat; collect_term t1))
                patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3333,t1,t2) ->
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
                (fun uu____3429  ->
                   match uu____3429 with | (uu____3434,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3437) -> collect_term t
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
         | FStar_Parser_AST.NamedTyp (uu____3493,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Assign (uu____3496,t) -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3499) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3505) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3511,uu____3512) ->
             collect_term t
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       and collect_pattern' uu___73_3520 =
         match uu___73_3520 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3521 -> ()
         | FStar_Parser_AST.PatConst uu____3522 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3530 -> ()
         | FStar_Parser_AST.PatName uu____3537 -> ()
         | FStar_Parser_AST.PatTvar uu____3538 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3552) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3571  ->
                  match uu____3571 with | (uu____3576,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,t) ->
             (collect_pattern p; collect_term t)
       and collect_branches bs = FStar_List.iter collect_branch bs
       and collect_branch uu____3600 =
         match uu____3600 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2) in
       let uu____3618 = FStar_Parser_Driver.parse_file filename in
       match uu____3618 with
       | (ast,uu____3638) ->
           (collect_module ast;
            (let uu____3652 = FStar_ST.op_Bang deps in
             let uu____3719 = FStar_ST.op_Bang mo_roots in
             (uu____3652, uu____3719))))
let collect:
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2
  =
  fun all_cmd_line_files  ->
    let dep_graph = deps_empty () in
    let file_system_map = build_map all_cmd_line_files in
    let rec discover_one file_name =
      let uu____3815 =
        let uu____3816 = deps_try_find dep_graph file_name in
        uu____3816 = FStar_Pervasives_Native.None in
      if uu____3815
      then
        let uu____3833 = collect_one file_system_map file_name in
        match uu____3833 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name in
              let uu____3856 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name) in
              if uu____3856
              then FStar_List.append deps [UseInterface module_name]
              else deps in
            ((let uu____3861 =
                let uu____3866 = FStar_List.unique deps1 in
                (uu____3866, White) in
              deps_add_dep dep_graph file_name uu____3861);
             (let uu____3871 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files)
                  (FStar_List.append deps1 mo_roots) in
              FStar_List.iter discover_one uu____3871))
      else () in
    FStar_List.iter discover_one all_cmd_line_files;
    (let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec aux cycle filename =
         let uu____3904 =
           let uu____3909 = deps_try_find dep_graph filename in
           FStar_Util.must uu____3909 in
         match uu____3904 with
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
                   (let uu____3928 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____3928);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____3934 =
                      let uu____3937 = FStar_ST.op_Bang topologically_sorted in
                      filename :: uu____3937 in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____3934))) in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted in
     FStar_All.pipe_right all_cmd_line_files
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f in
             FStar_Options.add_verify_module m));
     (let uu____4140 = topological_dependences_of all_cmd_line_files in
      (uu____4140, (Mk (dep_graph, file_system_map, all_cmd_line_files)))))
let deps_of: deps -> Prims.string -> Prims.string Prims.list =
  fun uu____4153  ->
    fun f  ->
      match uu____4153 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
let hash_dependences:
  deps ->
    Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option
  =
  fun uu____4174  ->
    fun fn  ->
      match uu____4174 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let cache_file = cache_file_name fn in
          let digest_of_file1 fn1 =
            (let uu____4193 = FStar_Options.debug_any () in
             if uu____4193
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn1
             else ());
            FStar_Util.digest_of_file fn1 in
          let module_name = lowercase_module_name fn in
          let source_hash = digest_of_file1 fn in
          let interface_hash =
            let uu____4200 =
              (is_implementation fn) &&
                (has_interface file_system_map module_name) in
            if uu____4200
            then
              let uu____4203 =
                let uu____4204 =
                  let uu____4205 = interface_of file_system_map module_name in
                  FStar_Option.get uu____4205 in
                digest_of_file1 uu____4204 in
              [uu____4203]
            else [] in
          let binary_deps =
            let uu____4212 =
              dependences_of file_system_map deps all_cmd_line_files fn in
            FStar_All.pipe_right uu____4212
              (FStar_List.filter
                 (fun fn1  ->
                    let uu____4222 =
                      (is_interface fn1) &&
                        (let uu____4224 = lowercase_module_name fn1 in
                         uu____4224 = module_name) in
                    Prims.op_Negation uu____4222)) in
          let binary_deps1 =
            FStar_List.sortWith FStar_String.compare binary_deps in
          let rec hash_deps out uu___74_4242 =
            match uu___74_4242 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (source_hash :: interface_hash) out)
            | fn1::deps1 ->
                let fn2 = cache_file_name fn1 in
                if FStar_Util.file_exists fn2
                then
                  let uu____4262 =
                    let uu____4265 = digest_of_file1 fn2 in uu____4265 :: out in
                  hash_deps uu____4262 deps1
                else FStar_Pervasives_Native.None in
          hash_deps [] binary_deps1
let print_make: deps -> Prims.unit =
  fun uu____4271  ->
    match uu____4271 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4291 =
                  let uu____4296 = deps_try_find deps f in
                  FStar_All.pipe_right uu____4296 FStar_Option.get in
                match uu____4291 with
                | (f_deps,uu____4318) ->
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
  fun uu____4330  ->
    match uu____4330 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps in
        let output_ml_file fst_file =
          let ml_base_name =
            let uu____4346 =
              let uu____4347 =
                let uu____4350 = FStar_Util.basename fst_file in
                check_and_strip_suffix uu____4350 in
              FStar_Option.get uu____4347 in
            FStar_Util.replace_chars uu____4346 46 "_" in
          let dir =
            let uu____4353 = FStar_Options.output_dir () in
            match uu____4353 with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some x -> Prims.strcat x "/" in
          Prims.strcat dir (Prims.strcat ml_base_name ".ml") in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____4373 =
                   let uu____4378 = deps_try_find deps f in
                   FStar_All.pipe_right uu____4378 FStar_Option.get in
                 match uu____4373 with
                 | (f_deps,uu____4400) ->
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps in
                     let files1 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files in
                     ((let uu____4411 = is_interface f in
                       if uu____4411
                       then
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" f f
                           (FStar_String.concat "\\\n\t" files1)
                       else ());
                      (let uu____4414 = cache_file_name f in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4414 f
                         (FStar_String.concat " \\\n\t" files1));
                      (let uu____4415 = is_implementation f in
                       if uu____4415
                       then
                         let ml_base_name =
                           let uu____4417 =
                             let uu____4418 =
                               let uu____4421 = FStar_Util.basename f in
                               check_and_strip_suffix uu____4421 in
                             FStar_Option.get uu____4418 in
                           FStar_Util.replace_chars uu____4417 46 "_" in
                         let uu____4423 = output_ml_file f in
                         let uu____4424 = cache_file_name f in
                         FStar_Util.print2 "%s: %s\n\n" uu____4423 uu____4424
                       else ()))));
         (let all_fst_files =
            let uu____4429 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation) in
            FStar_All.pipe_right uu____4429
              (FStar_Util.sort_with FStar_String.compare) in
          let all_ml_files =
            let uu____4443 =
              FStar_All.pipe_right all_fst_files
                (FStar_List.collect
                   (fun fst_file  ->
                      let uu____4454 =
                        let uu____4455 = lowercase_module_name fst_file in
                        FStar_Options.should_extract uu____4455 in
                      if uu____4454
                      then
                        let uu____4458 = output_ml_file fst_file in
                        [uu____4458]
                      else [])) in
            FStar_All.pipe_right uu____4443
              (FStar_Util.sort_with FStar_String.compare) in
          (let uu____4465 =
             FStar_All.pipe_right all_fst_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n" uu____4465);
          (let uu____4468 =
             FStar_All.pipe_right all_ml_files
               (FStar_String.concat " \\\n\t") in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n" uu____4468)))
let print: deps -> Prims.unit =
  fun deps  ->
    let uu____4474 = FStar_Options.dep () in
    match uu____4474 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____4477 = deps in
        (match uu____4477 with
         | Mk (deps1,uu____4479,uu____4480) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____4485 ->
        FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()