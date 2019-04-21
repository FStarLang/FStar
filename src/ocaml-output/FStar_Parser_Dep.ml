open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____20 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____31 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____42 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____65 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____76 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____87 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____98 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____109 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____157 =
             (l > lext) &&
               (let uu____160 = FStar_String.substring f (l - lext) lext  in
                uu____160 = ext)
              in
           if uu____157
           then
             let uu____167 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____167
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____174 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____174 with
    | (FStar_Pervasives_Native.Some m)::uu____188 ->
        FStar_Pervasives_Native.Some m
    | uu____200 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____217 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____217 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____231 = is_interface f  in Prims.op_Negation uu____231 
let list_of_option :
  'Auu____238 .
    'Auu____238 FStar_Pervasives_Native.option -> 'Auu____238 Prims.list
  =
  fun uu___0_247  ->
    match uu___0_247 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____256 .
    ('Auu____256 FStar_Pervasives_Native.option * 'Auu____256
      FStar_Pervasives_Native.option) -> 'Auu____256 Prims.list
  =
  fun uu____271  ->
    match uu____271 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____299 =
      let uu____303 = FStar_Util.basename f  in
      check_and_strip_suffix uu____303  in
    match uu____299 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____310 =
          let uu____316 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____316)  in
        FStar_Errors.raise_err uu____310
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____330 = module_name_of_file f  in
    FStar_String.lowercase uu____330
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____343 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____343 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____346 ->
        let uu____349 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____349
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____389 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____412 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____435 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____458 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_476  ->
    match uu___1_476 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____495 . unit -> 'Auu____495 Prims.list =
  fun uu____498  -> [] 
type dep_node = {
  edges: dependences ;
  color: color }
let (__proj__Mkdep_node__item__edges : dep_node -> dependences) =
  fun projectee  -> match projectee with | { edges; color;_} -> edges 
let (__proj__Mkdep_node__item__color : dep_node -> color) =
  fun projectee  -> match projectee with | { edges; color;_} -> color 
type dependence_graph =
  | Deps of dep_node FStar_Util.smap 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee  -> true 
let (__proj__Deps__item___0 : dependence_graph -> dep_node FStar_Util.smap) =
  fun projectee  -> match projectee with | Deps _0 -> _0 
type parsing_data =
  {
  direct_deps: dependence Prims.list ;
  additional_roots: dependence Prims.list ;
  has_inline_for_extraction: Prims.bool }
let (__proj__Mkparsing_data__item__direct_deps :
  parsing_data -> dependence Prims.list) =
  fun projectee  ->
    match projectee with
    | { direct_deps; additional_roots; has_inline_for_extraction;_} ->
        direct_deps
  
let (__proj__Mkparsing_data__item__additional_roots :
  parsing_data -> dependence Prims.list) =
  fun projectee  ->
    match projectee with
    | { direct_deps; additional_roots; has_inline_for_extraction;_} ->
        additional_roots
  
let (__proj__Mkparsing_data__item__has_inline_for_extraction :
  parsing_data -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { direct_deps; additional_roots; has_inline_for_extraction;_} ->
        has_inline_for_extraction
  
let (empty_parsing_data : parsing_data) =
  {
    direct_deps = [];
    additional_roots = [];
    has_inline_for_extraction = false
  } 
type deps =
  {
  dep_graph: dependence_graph ;
  file_system_map: files_for_module_name ;
  cmd_line_files: file_name Prims.list ;
  all_files: file_name Prims.list ;
  interfaces_with_inlining: module_name Prims.list ;
  parse_results: parsing_data FStar_Util.smap }
let (__proj__Mkdeps__item__dep_graph : deps -> dependence_graph) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> dep_graph
  
let (__proj__Mkdeps__item__file_system_map : deps -> files_for_module_name) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> file_system_map
  
let (__proj__Mkdeps__item__cmd_line_files : deps -> file_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> cmd_line_files
  
let (__proj__Mkdeps__item__all_files : deps -> file_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> all_files
  
let (__proj__Mkdeps__item__interfaces_with_inlining :
  deps -> module_name Prims.list) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} ->
        interfaces_with_inlining
  
let (__proj__Mkdeps__item__parse_results :
  deps -> parsing_data FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> parse_results
  
let (deps_try_find :
  dependence_graph -> Prims.string -> dep_node FStar_Pervasives_Native.option)
  =
  fun uu____840  ->
    fun k  -> match uu____840 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____862  ->
    fun k  ->
      fun v1  -> match uu____862 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____877  -> match uu____877 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____889  ->
    let uu____890 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____890
  
let (mk_deps :
  dependence_graph ->
    files_for_module_name ->
      file_name Prims.list ->
        file_name Prims.list ->
          module_name Prims.list -> parsing_data FStar_Util.smap -> deps)
  =
  fun dg  ->
    fun fs  ->
      fun c  ->
        fun a  ->
          fun i  ->
            fun pr  ->
              {
                dep_graph = dg;
                file_system_map = fs;
                cmd_line_files = c;
                all_files = a;
                interfaces_with_inlining = i;
                parse_results = pr
              }
  
let (empty_deps : deps) =
  let uu____948 = deps_empty ()  in
  let uu____949 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____961 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____948 uu____949 [] [] [] uu____961 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___2_974  ->
    match uu___2_974 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
    | FriendImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1003 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1003 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1030) ->
          let uu____1052 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1052
      | FStar_Pervasives_Native.Some
          (uu____1055,FStar_Pervasives_Native.Some fn) ->
          let uu____1078 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1078
      | uu____1081 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1114 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1114 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1141) ->
          FStar_Pervasives_Native.Some iface
      | uu____1164 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1197 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1197 with
      | FStar_Pervasives_Native.Some
          (uu____1223,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1247 -> FStar_Pervasives_Native.None
  
let (interface_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps  -> fun key  -> interface_of_internal deps.file_system_map key 
let (implementation_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps  ->
    fun key  -> implementation_of_internal deps.file_system_map key
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____1308 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1308
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1328 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1328
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1363 =
      let uu____1367 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1367  in
    match uu____1363 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1378 =
            ((let uu____1382 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1382) &&
               (let uu____1388 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1388))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1391 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1391))
             in
          if uu____1378
          then
            let uu____1394 =
              let uu____1400 =
                let uu____1402 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1402
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1400)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1394
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1409 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1409
        then
          let uu____1415 =
            let uu____1421 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1421)
             in
          FStar_Errors.raise_err uu____1415
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____1457 = FStar_Util.smap_try_find memo x  in
    match uu____1457 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1484 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1484 FStar_Util.must
  
let (file_of_dep_aux :
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name)
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
                      (let uu____1538 = lowercase_module_name fn  in
                       key = uu____1538)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1557 = interface_of_internal file_system_map key  in
              (match uu____1557 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1564 =
                     let uu____1570 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1570)  in
                   FStar_Errors.raise_err uu____1564
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1580 =
                (cmd_line_has_impl key) &&
                  (let uu____1583 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1583)
                 in
              if uu____1580
              then
                let uu____1590 = FStar_Options.expose_interfaces ()  in
                (if uu____1590
                 then
                   let uu____1594 =
                     let uu____1596 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____1596  in
                   maybe_use_cache_of uu____1594
                 else
                   (let uu____1603 =
                      let uu____1609 =
                        let uu____1611 =
                          let uu____1613 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____1613  in
                        let uu____1618 =
                          let uu____1620 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____1620  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1611 uu____1618
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1609)
                       in
                    FStar_Errors.raise_err uu____1603))
              else
                (let uu____1630 =
                   let uu____1632 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____1632  in
                 maybe_use_cache_of uu____1630)
          | PreferInterface key ->
              let uu____1639 = implementation_of_internal file_system_map key
                 in
              (match uu____1639 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1645 =
                     let uu____1651 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1651)
                      in
                   FStar_Errors.raise_err uu____1645
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____1661 = implementation_of_internal file_system_map key
                 in
              (match uu____1661 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1667 =
                     let uu____1673 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1673)
                      in
                   FStar_Errors.raise_err uu____1667
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____1683 = implementation_of_internal file_system_map key
                 in
              (match uu____1683 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1689 =
                     let uu____1695 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1695)
                      in
                   FStar_Errors.raise_err uu____1689
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
  
let (file_of_dep :
  files_for_module_name -> file_name Prims.list -> dependence -> file_name) =
  file_of_dep_aux false 
let (dependences_of :
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list)
  =
  fun file_system_map  ->
    fun deps  ->
      fun all_cmd_line_files  ->
        fun fn  ->
          let uu____1756 = deps_try_find deps fn  in
          match uu____1756 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____1764;_} ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1778 =
       let uu____1780 =
         let uu____1782 =
           let uu____1784 =
             let uu____1788 =
               let uu____1792 = deps_keys graph  in
               FStar_List.unique uu____1792  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1806 =
                      let uu____1807 = deps_try_find graph k  in
                      FStar_Util.must uu____1807  in
                    uu____1806.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____1828 =
                      let uu____1830 = lowercase_module_name k  in
                      r uu____1830  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1828
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1788
              in
           FStar_String.concat "\n" uu____1784  in
         FStar_String.op_Hat uu____1782 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____1780  in
     FStar_Util.write_file "dep.graph" uu____1778)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____1851  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1877 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1877  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1917 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1917
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1954 =
              let uu____1960 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1960)  in
            FStar_Errors.raise_err uu____1954)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____2023 = FStar_Util.smap_try_find map1 key  in
      match uu____2023 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2070 = is_interface full_path  in
          if uu____2070
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2119 = is_interface full_path  in
          if uu____2119
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2161 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2179  ->
          match uu____2179 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2161);
    FStar_List.iter
      (fun f  ->
         let uu____2198 = lowercase_module_name f  in add_entry uu____2198 f)
      filenames;
    map1
  
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool)
  =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false  in
        let prefix2 = FStar_String.op_Hat prefix1 "."  in
        (let uu____2230 =
           let uu____2234 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2234  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2270 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2270  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2230);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2390 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2390 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2413 = string_of_lid l last1  in
      FStar_String.lowercase uu____2413
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2422 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2422
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2444 =
        let uu____2446 =
          let uu____2448 =
            let uu____2450 =
              let uu____2454 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2454  in
            FStar_Util.must uu____2450  in
          FStar_String.lowercase uu____2448  in
        uu____2446 <> k'  in
      if uu____2444
      then
        let uu____2459 = FStar_Ident.range_of_lid lid  in
        let uu____2460 =
          let uu____2466 =
            let uu____2468 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2468 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2466)  in
        FStar_Errors.log_issue uu____2459 uu____2460
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2484 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2506 = FStar_Options.prims_basename ()  in
      let uu____2508 =
        let uu____2512 = FStar_Options.pervasives_basename ()  in
        let uu____2514 =
          let uu____2518 = FStar_Options.pervasives_native_basename ()  in
          [uu____2518]  in
        uu____2512 :: uu____2514  in
      uu____2506 :: uu____2508  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2561 =
         let uu____2564 = lowercase_module_name full_filename  in
         namespace_of_module uu____2564  in
       match uu____2561 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2603 -> d = d'
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        parsing_data)
  =
  fun original_map  ->
    fun filename  ->
      fun get_parsing_data_from_cache  ->
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____2643 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____2643
        then
          ((let uu____2650 = FStar_Options.debug_any ()  in
            if uu____2650
            then
              FStar_Util.print1
                "Reading parsing data for %s from its checked file\n"
                filename
            else ());
           FStar_All.pipe_right data_from_cache FStar_Util.must)
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____2685 =
             let uu____2686 = is_interface filename  in
             if uu____2686
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____2808 =
               let uu____2810 =
                 let uu____2812 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____2812  in
               Prims.op_Negation uu____2810  in
             if uu____2808
             then
               let uu____2839 =
                 let uu____2842 = FStar_ST.op_Bang deps1  in d :: uu____2842
                  in
               FStar_ST.op_Colon_Equals deps1 uu____2839
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____2939 = resolve_module_name original_or_working_map key
                in
             match uu____2939 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____2949 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____2949
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____2955 -> false  in
           let record_open_module let_open lid =
             let uu____2974 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____2974
             then true
             else
               (if let_open
                then
                  (let uu____2983 = FStar_Ident.range_of_lid lid  in
                   let uu____2984 =
                     let uu____2990 =
                       let uu____2992 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____2992
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____2990)
                      in
                   FStar_Errors.log_issue uu____2983 uu____2984)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____3012 = FStar_Ident.range_of_lid lid  in
               let uu____3013 =
                 let uu____3019 =
                   let uu____3021 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____3021
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____3019)
                  in
               FStar_Errors.log_issue uu____3012 uu____3013
             else ()  in
           let record_open let_open lid =
             let uu____3041 = record_open_module let_open lid  in
             if uu____3041
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____3058 =
             match uu____3058 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____3065 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____3082 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____3082  in
             let alias = lowercase_join_longident lid true  in
             let uu____3087 = FStar_Util.smap_try_find original_map alias  in
             match uu____3087 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3155 = FStar_Ident.range_of_lid lid  in
                   let uu____3156 =
                     let uu____3162 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____3162)
                      in
                   FStar_Errors.log_issue uu____3155 uu____3156);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____3173 = add_dependence_edge working_map module_name  in
             if uu____3173
             then ()
             else
               (let uu____3178 = FStar_Options.debug_any ()  in
                if uu____3178
                then
                  let uu____3181 = FStar_Ident.range_of_lid module_name  in
                  let uu____3182 =
                    let uu____3188 =
                      let uu____3190 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____3190
                       in
                    (FStar_Errors.Warning_UnboundModuleReference, uu____3188)
                     in
                  FStar_Errors.log_issue uu____3181 uu____3182
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____3202 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___3_3330 =
              match uu___3_3330 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____3341 =
                        let uu____3343 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____3343
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____3349) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____3360 =
                        let uu____3362 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____3362
                         in
                      ())
                   else ();
                   collect_decls decls)
            
            and collect_decls decls =
              FStar_List.iter
                (fun x  ->
                   collect_decl x.FStar_Parser_AST.d;
                   FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                   if
                     FStar_List.contains
                       FStar_Parser_AST.Inline_for_extraction
                       x.FStar_Parser_AST.quals
                   then set_interface_inlining ()
                   else ()) decls
            
            and collect_decl d =
              match d with
              | FStar_Parser_AST.Include lid -> record_open false lid
              | FStar_Parser_AST.Open lid -> record_open false lid
              | FStar_Parser_AST.Friend lid ->
                  let uu____3384 =
                    let uu____3385 = lowercase_join_longident lid true  in
                    FriendImplementation uu____3385  in
                  add_dep deps uu____3384
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____3390 = record_module_alias ident lid  in
                  if uu____3390
                  then
                    let uu____3393 =
                      let uu____3394 = lowercase_join_longident lid true  in
                      dep_edge uu____3394  in
                    add_dep deps uu____3393
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____3399,patterms) ->
                  FStar_List.iter
                    (fun uu____3421  ->
                       match uu____3421 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____3430,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____3436,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3438;
                    FStar_Parser_AST.mdest = uu____3439;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3441;
                    FStar_Parser_AST.mdest = uu____3442;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____3444,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____3446;
                    FStar_Parser_AST.mdest = uu____3447;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____3451,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____3490  ->
                           match uu____3490 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____3503,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____3510 -> ()
              | FStar_Parser_AST.Pragma uu____3511 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____3514 =
                      let uu____3516 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____3516 > (Prims.parse_int "1")  in
                    if uu____3514
                    then
                      let uu____3541 =
                        let uu____3547 =
                          let uu____3549 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____3549
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____3547)  in
                      let uu____3554 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____3541 uu____3554
                    else ()))
            
            and collect_tycon uu___4_3557 =
              match uu___4_3557 with
              | FStar_Parser_AST.TyconAbstract (uu____3558,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____3570,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____3584,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____3630  ->
                        match uu____3630 with
                        | (uu____3639,t,uu____3641) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____3646,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____3708  ->
                        match uu____3708 with
                        | (uu____3722,t,uu____3724,uu____3725) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___5_3736 =
              match uu___5_3736 with
              | FStar_Parser_AST.DefineEffect (uu____3737,binders,t,decls) ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____3751,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____3764,t);
                   FStar_Parser_AST.brange = uu____3766;
                   FStar_Parser_AST.blevel = uu____3767;
                   FStar_Parser_AST.aqual = uu____3768;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____3771,t);
                   FStar_Parser_AST.brange = uu____3773;
                   FStar_Parser_AST.blevel = uu____3774;
                   FStar_Parser_AST.aqual = uu____3775;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____3779;
                   FStar_Parser_AST.blevel = uu____3780;
                   FStar_Parser_AST.aqual = uu____3781;_} -> collect_term t
               | uu____3784 -> ())
            
            and collect_aqual uu___6_3785 =
              match uu___6_3785 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____3789 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___7_3793 =
              match uu___7_3793 with
              | FStar_Const.Const_int
                  (uu____3794,FStar_Pervasives_Native.Some
                   (signedness,width))
                  ->
                  let u =
                    match signedness with
                    | FStar_Const.Unsigned  -> "u"
                    | FStar_Const.Signed  -> ""  in
                  let w =
                    match width with
                    | FStar_Const.Int8  -> "8"
                    | FStar_Const.Int16  -> "16"
                    | FStar_Const.Int32  -> "32"
                    | FStar_Const.Int64  -> "64"  in
                  let uu____3821 =
                    let uu____3822 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____3822  in
                  add_dep deps uu____3821
              | FStar_Const.Const_char uu____3825 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____3828 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____3830 -> ()
            
            and collect_term' uu___10_3831 =
              match uu___10_3831 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____3840 =
                      let uu____3842 = FStar_Ident.text_of_id s  in
                      uu____3842 = "@"  in
                    if uu____3840
                    then
                      let uu____3847 =
                        let uu____3848 =
                          let uu____3849 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____3849
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____3848  in
                      collect_term' uu____3847
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____3853 -> ()
              | FStar_Parser_AST.Uvar uu____3854 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____3857) -> record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____3882  ->
                        match uu____3882 with
                        | (t,uu____3888) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____3898) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____3900,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____3950  ->
                        match uu____3950 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____3979 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____3989,t1,t2) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Seq (t1,t2) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.If (t1,t2,t3) ->
                  (collect_term t1; collect_term t2; collect_term t3)
              | FStar_Parser_AST.Match (t,bs) ->
                  (collect_term t; collect_branches bs)
              | FStar_Parser_AST.TryWith (t,bs) ->
                  (collect_term t; collect_branches bs)
              | FStar_Parser_AST.Ascribed
                  (t1,t2,FStar_Pervasives_Native.None ) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Ascribed
                  (t1,t2,FStar_Pervasives_Native.Some tac) ->
                  (collect_term t1; collect_term t2; collect_term tac)
              | FStar_Parser_AST.Record (t,idterms) ->
                  (FStar_Util.iter_opt t collect_term;
                   FStar_List.iter
                     (fun uu____4085  ->
                        match uu____4085 with
                        | (uu____4090,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____4093) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___8_4122  ->
                        match uu___8_4122 with
                        | FStar_Util.Inl b -> collect_binder b
                        | FStar_Util.Inr t1 -> collect_term t1) binders;
                   collect_term t)
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
              | FStar_Parser_AST.NamedTyp (uu____4170,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____4174) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____4182) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____4190,uu____4191) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____4197) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____4211 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____4211);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___9_4221  ->
                        match uu___9_4221 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___11_4231 =
              match uu___11_4231 with
              | FStar_Parser_AST.PatVar (uu____4232,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____4238,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____4247 -> ()
              | FStar_Parser_AST.PatConst uu____4248 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____4256 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____4264) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____4285  ->
                       match uu____4285 with
                       | (uu____4290,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____4335 =
              match uu____4335 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____4353 = FStar_Parser_Driver.parse_file filename  in
            match uu____4353 with
            | (ast,uu____4366) ->
                let mname = lowercase_module_name filename  in
                ((let uu____4384 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____4384
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____4390 = FStar_ST.op_Bang deps  in
                  let uu____4416 = FStar_ST.op_Bang mo_roots  in
                  let uu____4442 = FStar_ST.op_Bang has_inline_for_extraction
                     in
                  {
                    direct_deps = uu____4390;
                    additional_roots = uu____4416;
                    has_inline_for_extraction = uu____4442
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____4481 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____4481 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____4603 = dep_graph  in
    match uu____4603 with
    | Deps g -> let uu____4607 = FStar_Util.smap_copy g  in Deps uu____4607
  
let (topological_dependences_of :
  files_for_module_name ->
    dependence_graph ->
      Prims.string Prims.list ->
        file_name Prims.list ->
          Prims.bool -> (file_name Prims.list * Prims.bool))
  =
  fun file_system_map  ->
    fun dep_graph  ->
      fun interfaces_needing_inlining  ->
        fun root_files  ->
          fun for_extraction  ->
            let rec all_friend_deps_1 dep_graph1 cycle uu____4752 filename =
              match uu____4752 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____4793 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____4793  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____4824 = FStar_Options.debug_any ()  in
                         if uu____4824
                         then
                           let uu____4827 =
                             let uu____4829 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____4829  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____4827
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___842_4840 = dep_node  in
                           { edges = (uu___842_4840.edges); color = Gray });
                        (let uu____4841 =
                           let uu____4852 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____4852
                            in
                         match uu____4841 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___848_4888 = dep_node  in
                                 {
                                   edges = (uu___848_4888.edges);
                                   color = Black
                                 });
                              (let uu____4890 = FStar_Options.debug_any ()
                                  in
                               if uu____4890
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____4896 =
                                 let uu____4900 =
                                   FStar_List.collect
                                     (fun uu___12_4907  ->
                                        match uu___12_4907 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____4900 all_friends1
                                  in
                               (uu____4896, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____4973 = FStar_Options.debug_any ()  in
             if uu____4973
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____5002 = deps  in
               match uu____5002 with
               | Deps dg ->
                   let uu____5006 = deps_empty ()  in
                   (match uu____5006 with
                    | Deps dg' ->
                        let widen_one deps1 =
                          FStar_All.pipe_right deps1
                            (FStar_List.map
                               (fun d  ->
                                  match d with
                                  | PreferInterface m when
                                      (FStar_List.contains m friends) &&
                                        (has_implementation file_system_map m)
                                      ->
                                      (FStar_ST.op_Colon_Equals widened true;
                                       FriendImplementation m)
                                  | uu____5056 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____5064  ->
                                  let uu____5066 =
                                    let uu___883_5067 = dep_node  in
                                    let uu____5068 = widen_one dep_node.edges
                                       in
                                    { edges = uu____5068; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____5066)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____5070 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____5070
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____5075 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____5075 with
             | (friends,all_files_0) ->
                 ((let uu____5118 = FStar_Options.debug_any ()  in
                   if uu____5118
                   then
                     let uu____5121 =
                       let uu____5123 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____5123  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____5121
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____5142 =
                     (let uu____5154 = FStar_Options.debug_any ()  in
                      if uu____5154
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____5142 with
                   | (uu____5177,all_files) ->
                       ((let uu____5192 = FStar_Options.debug_any ()  in
                         if uu____5192
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____5199 = FStar_ST.op_Bang widened  in
                         (all_files, uu____5199))))))
  
let (collect :
  Prims.string Prims.list ->
    (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
      (Prims.string Prims.list * deps))
  =
  fun all_cmd_line_files  ->
    fun get_parsing_data_from_cache  ->
      let all_cmd_line_files1 =
        FStar_All.pipe_right all_cmd_line_files
          (FStar_List.map
             (fun fn  ->
                let uu____5285 = FStar_Options.find_file fn  in
                match uu____5285 with
                | FStar_Pervasives_Native.None  ->
                    let uu____5291 =
                      let uu____5297 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____5297)
                       in
                    FStar_Errors.raise_err uu____5291
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____5327 =
          let uu____5331 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____5331  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____5327  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____5398 =
          let uu____5400 = deps_try_find dep_graph file_name  in
          uu____5400 = FStar_Pervasives_Native.None  in
        if uu____5398
        then
          let uu____5406 =
            let uu____5418 =
              let uu____5432 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____5432 file_name  in
            match uu____5418 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____5406 with
          | (deps,mo_roots,needs_interface_inlining) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name
                 {
                   direct_deps = deps;
                   additional_roots = mo_roots;
                   has_inline_for_extraction = needs_interface_inlining
                 };
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____5576 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____5576
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____5584 = FStar_List.unique deps1  in
                  { edges = uu____5584; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____5586 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____5586)))
        else ()  in
      FStar_Options.profile
        (fun uu____5596  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____5599  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____5631 =
            let uu____5637 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____5637)  in
          FStar_Errors.raise_err uu____5631)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____5674 = deps_try_find dep_graph1 filename  in
             match uu____5674 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____5678 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____5678
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____5692 =
                           implementation_of_internal file_system_map f  in
                         (match uu____5692 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____5703 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____5709 =
                           implementation_of_internal file_system_map f  in
                         (match uu____5709 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____5720 -> [x; UseImplementation f])
                     | uu____5724 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___969_5727 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____5729 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____5729);
                deps_add_dep dep_graph1 filename
                  (let uu___974_5739 = node  in
                   { edges = direct_deps; color = Black }))
            in
         FStar_List.iter (aux []) all_command_line_files  in
       full_cycle_detection all_cmd_line_files1;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____5783 =
          FStar_Options.profile
            (fun uu____5802  ->
               let uu____5803 =
                 let uu____5805 = FStar_Options.codegen ()  in
                 uu____5805 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____5803)
            (fun uu____5811  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____5783 with
        | (all_files,uu____5829) ->
            ((let uu____5839 = FStar_Options.debug_any ()  in
              if uu____5839
              then
                FStar_Util.print1 "Interfaces needing inlining: %s\n"
                  (FStar_String.concat ", " inlining_ifaces)
              else ());
             (all_files,
               (mk_deps dep_graph file_system_map all_cmd_line_files1
                  all_files inlining_ifaces parse_results)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun deps  ->
    fun f  ->
      dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files
        f
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____5892 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____5918  ->
              match uu____5918 with
              | (m,d) ->
                  let uu____5932 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____5932))
       in
    FStar_All.pipe_right uu____5892 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun deps  ->
    let file_system_map = deps.file_system_map  in
    let all_cmd_line_files = deps.cmd_line_files  in
    let deps1 = deps.dep_graph  in
    let keys = deps_keys deps1  in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun f  ->
            let dep_node =
              let uu____5967 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____5967 FStar_Option.get  in
            let files =
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                dep_node.edges
               in
            let files1 =
              FStar_List.map (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                files
               in
            FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))
  
let (print_raw : deps -> unit) =
  fun deps  ->
    let uu____5996 = deps.dep_graph  in
    match uu____5996 with
    | Deps deps1 ->
        let uu____6000 =
          let uu____6002 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____6020 =
                       let uu____6022 =
                         let uu____6024 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____6024
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____6022
                        in
                     uu____6020 :: out) []
             in
          FStar_All.pipe_right uu____6002 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____6000 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____6096 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____6096) ||
          (let uu____6103 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____6103)
         in
      let mark_visiting lc_module_name =
        let ml_file_opt =
          FStar_Util.smap_try_find remaining_output_files lc_module_name  in
        FStar_Util.smap_remove remaining_output_files lc_module_name;
        FStar_Util.smap_add visited_other_modules lc_module_name true;
        ml_file_opt  in
      let emit_output_file_opt ml_file_opt =
        match ml_file_opt with
        | FStar_Pervasives_Native.None  -> ()
        | FStar_Pervasives_Native.Some ml_file ->
            let uu____6146 =
              let uu____6150 = FStar_ST.op_Bang order  in ml_file ::
                uu____6150
               in
            FStar_ST.op_Colon_Equals order uu____6146
         in
      let rec aux uu___13_6213 =
        match uu___13_6213 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____6241 = deps_try_find deps.dep_graph file_name  in
                  (match uu____6241 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____6244 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____6244
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____6248;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____6257 = should_visit lc_module_name  in
              if uu____6257
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____6265 = implementation_of deps lc_module_name  in
                  visit_file uu____6265);
                 (let uu____6270 = interface_of deps lc_module_name  in
                  visit_file uu____6270);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____6282 = FStar_ST.op_Bang order  in FStar_List.rev uu____6282)
       in
    let sb =
      let uu____6313 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____6313  in
    let pr str =
      let uu____6323 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____6323  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____6376 =
          let uu____6378 =
            let uu____6382 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____6382  in
          FStar_Option.get uu____6378  in
        FStar_Util.replace_chars uu____6376 46 "_"  in
      let uu____6387 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____6387  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____6409 = output_file ".ml" f  in norm_path uu____6409  in
    let output_krml_file f =
      let uu____6421 = output_file ".krml" f  in norm_path uu____6421  in
    let output_cmx_file f =
      let uu____6433 = output_file ".cmx" f  in norm_path uu____6433  in
    let cache_file f =
      let uu____6445 = cache_file_name f  in norm_path uu____6445  in
    let all_checked_files =
      FStar_All.pipe_right keys
        (FStar_List.fold_left
           (fun all_checked_files  ->
              fun file_name  ->
                let process_one_key uu____6478 =
                  let dep_node =
                    let uu____6480 = deps_try_find deps.dep_graph file_name
                       in
                    FStar_All.pipe_right uu____6480 FStar_Option.get  in
                  let iface_deps =
                    let uu____6490 = is_interface file_name  in
                    if uu____6490
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____6501 =
                         let uu____6505 = lowercase_module_name file_name  in
                         interface_of deps uu____6505  in
                       match uu____6501 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some iface ->
                           let uu____6517 =
                             let uu____6520 =
                               let uu____6521 =
                                 deps_try_find deps.dep_graph iface  in
                               FStar_Option.get uu____6521  in
                             uu____6520.edges  in
                           FStar_Pervasives_Native.Some uu____6517)
                     in
                  let iface_deps1 =
                    FStar_Util.map_opt iface_deps
                      (FStar_List.filter
                         (fun iface_dep  ->
                            let uu____6538 =
                              FStar_Util.for_some (dep_subsumed_by iface_dep)
                                dep_node.edges
                               in
                            Prims.op_Negation uu____6538))
                     in
                  let norm_f = norm_path file_name  in
                  let files =
                    FStar_List.map
                      (file_of_dep_aux true deps.file_system_map
                         deps.cmd_line_files) dep_node.edges
                     in
                  let files1 =
                    match iface_deps1 with
                    | FStar_Pervasives_Native.None  -> files
                    | FStar_Pervasives_Native.Some iface_deps2 ->
                        let iface_files =
                          FStar_List.map
                            (file_of_dep_aux true deps.file_system_map
                               deps.cmd_line_files) iface_deps2
                           in
                        FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                          (FStar_List.append files iface_files)
                     in
                  let files2 = FStar_List.map norm_path files1  in
                  let files3 =
                    FStar_List.map
                      (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files2
                     in
                  let files4 =
                    FStar_Options.profile
                      (fun uu____6598  -> FStar_String.concat "\\\n\t" files3)
                      (fun uu____6601  -> "Dependence analysis: concat files")
                     in
                  let cache_file_name1 = cache_file file_name  in
                  let all_checked_files1 =
                    let uu____6610 =
                      let uu____6612 =
                        let uu____6614 = module_name_of_file file_name  in
                        FStar_Options.should_be_already_cached uu____6614  in
                      Prims.op_Negation uu____6612  in
                    if uu____6610
                    then
                      (print_entry cache_file_name1 norm_f files4;
                       cache_file_name1
                       ::
                       all_checked_files)
                    else all_checked_files  in
                  let uu____6624 =
                    let uu____6633 = FStar_Options.cmi ()  in
                    if uu____6633
                    then
                      FStar_Options.profile
                        (fun uu____6653  ->
                           topological_dependences_of deps.file_system_map
                             deps.dep_graph deps.interfaces_with_inlining
                             [file_name] true)
                        (fun uu____6658  ->
                           "Dependence analysis: cmi, second topological sort")
                    else
                      (let maybe_widen_deps f_deps =
                         FStar_List.map
                           (fun dep1  ->
                              file_of_dep_aux false deps.file_system_map
                                deps.cmd_line_files dep1) f_deps
                          in
                       let fst_files = maybe_widen_deps dep_node.edges  in
                       let fst_files_from_iface =
                         match iface_deps1 with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some iface_deps2 ->
                             maybe_widen_deps iface_deps2
                          in
                       let uu____6702 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           (FStar_List.append fst_files fst_files_from_iface)
                          in
                       (uu____6702, false))
                     in
                  match uu____6624 with
                  | (all_fst_files_dep,widened) ->
                      let all_checked_fst_dep_files =
                        FStar_All.pipe_right all_fst_files_dep
                          (FStar_List.map cache_file)
                         in
                      let all_checked_fst_dep_files_string =
                        FStar_String.concat " \\\n\t"
                          all_checked_fst_dep_files
                         in
                      ((let uu____6749 = is_implementation file_name  in
                        if uu____6749
                        then
                          ((let uu____6753 =
                              (FStar_Options.cmi ()) && widened  in
                            if uu____6753
                            then
                              ((let uu____6757 = output_ml_file file_name  in
                                print_entry uu____6757 cache_file_name1
                                  all_checked_fst_dep_files_string);
                               (let uu____6759 = output_krml_file file_name
                                   in
                                print_entry uu____6759 cache_file_name1
                                  all_checked_fst_dep_files_string))
                            else
                              ((let uu____6764 = output_ml_file file_name  in
                                print_entry uu____6764 cache_file_name1 "");
                               (let uu____6767 = output_krml_file file_name
                                   in
                                print_entry uu____6767 cache_file_name1 "")));
                           (let cmx_files =
                              let extracted_fst_files =
                                FStar_All.pipe_right all_fst_files_dep
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____6792 =
                                           lowercase_module_name df  in
                                         let uu____6794 =
                                           lowercase_module_name file_name
                                            in
                                         uu____6792 <> uu____6794) &&
                                          (let uu____6798 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____6798)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            let uu____6808 =
                              let uu____6810 =
                                lowercase_module_name file_name  in
                              FStar_Options.should_extract uu____6810  in
                            if uu____6808
                            then
                              let cmx_files1 =
                                FStar_String.concat "\\\n\t" cmx_files  in
                              let uu____6816 = output_cmx_file file_name  in
                              let uu____6818 = output_ml_file file_name  in
                              print_entry uu____6816 uu____6818 cmx_files1
                            else ()))
                        else
                          (let uu____6824 =
                             (let uu____6828 =
                                let uu____6830 =
                                  lowercase_module_name file_name  in
                                has_implementation deps.file_system_map
                                  uu____6830
                                 in
                              Prims.op_Negation uu____6828) &&
                               (is_interface file_name)
                              in
                           if uu____6824
                           then
                             let uu____6833 =
                               (FStar_Options.cmi ()) && (widened || true)
                                in
                             (if uu____6833
                              then
                                let uu____6837 = output_krml_file file_name
                                   in
                                print_entry uu____6837 cache_file_name1
                                  all_checked_fst_dep_files_string
                              else
                                (let uu____6841 = output_krml_file file_name
                                    in
                                 print_entry uu____6841 cache_file_name1 ""))
                           else ()));
                       all_checked_files1)
                   in
                FStar_Options.profile process_one_key
                  (fun uu____6850  ->
                     FStar_Util.format1 "Dependence analysis: output key %s"
                       file_name)) [])
       in
    let all_fst_files =
      let uu____6860 =
        FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
      FStar_All.pipe_right uu____6860
        (FStar_Util.sort_with FStar_String.compare)
       in
    let all_ml_files =
      let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right all_fst_files
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____6901 = FStar_Options.should_extract mname  in
              if uu____6901
              then
                let uu____6904 = output_ml_file fst_file  in
                FStar_Util.smap_add ml_file_map mname uu____6904
              else ()));
      sort_output_files ml_file_map  in
    let all_krml_files =
      let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____6931 = output_krml_file fst_file  in
              FStar_Util.smap_add krml_file_map mname uu____6931));
      sort_output_files krml_file_map  in
    let print_all tag files =
      pr tag;
      pr "=\\\n\t";
      FStar_List.iter (fun f  -> pr (norm_path f); pr " \\\n\t") files;
      pr "\n"  in
    print_all "ALL_FST_FILES" all_fst_files;
    print_all "ALL_CHECKED_FILES" all_checked_files;
    print_all "ALL_ML_FILES" all_ml_files;
    print_all "ALL_KRML_FILES" all_krml_files;
    FStar_StringBuffer.output_channel FStar_Util.stdout sb
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____6979 = FStar_Options.dep ()  in
    match uu____6979 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____6988  -> print_full deps)
          (fun uu____6990  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____6996 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  
let (print_fsmap :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap -> Prims.string)
  =
  fun fsmap  ->
    FStar_Util.smap_fold fsmap
      (fun k  ->
         fun uu____7051  ->
           fun s  ->
             match uu____7051 with
             | (v0,v1) ->
                 let uu____7080 =
                   let uu____7082 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____7082  in
                 FStar_String.op_Hat s uu____7080) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____7103 =
        let uu____7105 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____7105  in
      has_interface deps.file_system_map uu____7103
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____7121 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____7121  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____7132 =
                   let uu____7134 = module_name_of_file f  in
                   FStar_String.lowercase uu____7134  in
                 uu____7132 = m)))
  