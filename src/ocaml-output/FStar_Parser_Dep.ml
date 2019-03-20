open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____45955 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____45966 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____45977 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____46000 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____46011 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____46022 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____46033 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____46044 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____46092 =
             (l > lext) &&
               (let uu____46095 = FStar_String.substring f (l - lext) lext
                   in
                uu____46095 = ext)
              in
           if uu____46092
           then
             let uu____46102 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____46102
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____46109 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____46109 with
    | (FStar_Pervasives_Native.Some m)::uu____46123 ->
        FStar_Pervasives_Native.Some m
    | uu____46135 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46152 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____46152 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46166 = is_interface f  in Prims.op_Negation uu____46166
  
let list_of_option :
  'Auu____46173 .
    'Auu____46173 FStar_Pervasives_Native.option -> 'Auu____46173 Prims.list
  =
  fun uu___423_46182  ->
    match uu___423_46182 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____46191 .
    ('Auu____46191 FStar_Pervasives_Native.option * 'Auu____46191
      FStar_Pervasives_Native.option) -> 'Auu____46191 Prims.list
  =
  fun uu____46206  ->
    match uu____46206 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46234 =
      let uu____46238 = FStar_Util.basename f  in
      check_and_strip_suffix uu____46238  in
    match uu____46234 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____46245 =
          let uu____46251 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____46251)  in
        FStar_Errors.raise_err uu____46245
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46265 = module_name_of_file f  in
    FStar_String.lowercase uu____46265
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____46278 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____46278 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____46281 ->
        let uu____46284 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____46284
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____46324 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____46347 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____46370 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____46393 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_46411  ->
    match uu___424_46411 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____46430 . unit -> 'Auu____46430 Prims.list =
  fun uu____46433  -> [] 
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
  fun uu____46775  ->
    fun k  -> match uu____46775 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____46797  ->
    fun k  ->
      fun v1  ->
        match uu____46797 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____46812  ->
    match uu____46812 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____46824  ->
    let uu____46825 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____46825
  
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
  let uu____46883 = deps_empty ()  in
  let uu____46884 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____46896 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____46883 uu____46884 [] [] [] uu____46896 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_46909  ->
    match uu___425_46909 with
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
      let uu____46938 = FStar_Util.smap_try_find file_system_map key  in
      match uu____46938 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____46965) ->
          let uu____46987 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____46987
      | FStar_Pervasives_Native.Some
          (uu____46990,FStar_Pervasives_Native.Some fn) ->
          let uu____47013 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____47013
      | uu____47016 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47049 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47049 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____47076) ->
          FStar_Pervasives_Native.Some iface
      | uu____47099 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47132 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47132 with
      | FStar_Pervasives_Native.Some
          (uu____47158,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____47182 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____47211 = interface_of file_system_map key  in
      FStar_Option.isSome uu____47211
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47231 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____47231
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____47266 =
      let uu____47270 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____47270  in
    match uu____47266 with
    | FStar_Pervasives_Native.Some path ->
        let uu____47278 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____47278
        then path
        else
          (let uu____47286 =
             let uu____47288 = FStar_Options.prepend_cache_dir cache_fn  in
             path <> uu____47288  in
           if uu____47286
           then
             let uu____47293 =
               let uu____47299 =
                 FStar_Util.format2
                   "Did not expected %s to be already checked, but found it in an unexpected location %s"
                   mname path
                  in
               (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                 uu____47299)
                in
             FStar_Errors.raise_err uu____47293
           else path)
    | FStar_Pervasives_Native.None  ->
        let uu____47307 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____47307
        then
          let uu____47313 =
            let uu____47319 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____47319)
             in
          FStar_Errors.raise_err uu____47313
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____47355 = FStar_Util.smap_try_find memo x  in
    match uu____47355 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____47382 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____47382 FStar_Util.must
  
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
                      (let uu____47436 = lowercase_module_name fn  in
                       key = uu____47436)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____47455 = interface_of file_system_map key  in
              (match uu____47455 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47462 =
                     let uu____47468 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____47468)  in
                   FStar_Errors.raise_err uu____47462
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____47478 =
                (cmd_line_has_impl key) &&
                  (let uu____47481 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____47481)
                 in
              if uu____47478
              then
                let uu____47488 = FStar_Options.expose_interfaces ()  in
                (if uu____47488
                 then
                   let uu____47492 =
                     let uu____47494 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____47494  in
                   maybe_use_cache_of uu____47492
                 else
                   (let uu____47501 =
                      let uu____47507 =
                        let uu____47509 =
                          let uu____47511 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____47511  in
                        let uu____47516 =
                          let uu____47518 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____47518  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____47509 uu____47516
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____47507)
                       in
                    FStar_Errors.raise_err uu____47501))
              else
                (let uu____47528 =
                   let uu____47530 = interface_of file_system_map key  in
                   FStar_Option.get uu____47530  in
                 maybe_use_cache_of uu____47528)
          | PreferInterface key ->
              let uu____47537 = implementation_of file_system_map key  in
              (match uu____47537 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47543 =
                     let uu____47549 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47549)
                      in
                   FStar_Errors.raise_err uu____47543
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____47559 = implementation_of file_system_map key  in
              (match uu____47559 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47565 =
                     let uu____47571 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47571)
                      in
                   FStar_Errors.raise_err uu____47565
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____47581 = implementation_of file_system_map key  in
              (match uu____47581 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47587 =
                     let uu____47593 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47593)
                      in
                   FStar_Errors.raise_err uu____47587
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
          let uu____47654 = deps_try_find deps fn  in
          match uu____47654 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____47662;_} ->
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
    (let uu____47676 =
       let uu____47678 =
         let uu____47680 =
           let uu____47682 =
             let uu____47686 =
               let uu____47690 = deps_keys graph  in
               FStar_List.unique uu____47690  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____47704 =
                      let uu____47705 = deps_try_find graph k  in
                      FStar_Util.must uu____47705  in
                    uu____47704.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____47726 =
                      let uu____47728 = lowercase_module_name k  in
                      r uu____47728  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____47726
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____47686
              in
           FStar_String.concat "\n" uu____47682  in
         FStar_String.op_Hat uu____47680 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____47678  in
     FStar_Util.write_file "dep.graph" uu____47676)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____47749  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____47775 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____47775  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____47815 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____47815
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____47852 =
              let uu____47858 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____47858)  in
            FStar_Errors.raise_err uu____47852)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____47921 = FStar_Util.smap_try_find map1 key  in
      match uu____47921 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____47968 = is_interface full_path  in
          if uu____47968
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____48017 = is_interface full_path  in
          if uu____48017
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____48059 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____48077  ->
          match uu____48077 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____48059);
    FStar_List.iter
      (fun f  ->
         let uu____48096 = lowercase_module_name f  in
         add_entry uu____48096 f) filenames;
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
        (let uu____48128 =
           let uu____48132 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____48132  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____48168 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____48168  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____48128);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____48288 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____48288 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____48311 = string_of_lid l last1  in
      FStar_String.lowercase uu____48311
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____48320 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____48320
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____48342 =
        let uu____48344 =
          let uu____48346 =
            let uu____48348 =
              let uu____48352 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____48352  in
            FStar_Util.must uu____48348  in
          FStar_String.lowercase uu____48346  in
        uu____48344 <> k'  in
      if uu____48342
      then
        let uu____48357 = FStar_Ident.range_of_lid lid  in
        let uu____48358 =
          let uu____48364 =
            let uu____48366 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____48366 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____48364)  in
        FStar_Errors.log_issue uu____48357 uu____48358
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____48382 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____48404 = FStar_Options.prims_basename ()  in
      let uu____48406 =
        let uu____48410 = FStar_Options.pervasives_basename ()  in
        let uu____48412 =
          let uu____48416 = FStar_Options.pervasives_native_basename ()  in
          [uu____48416]  in
        uu____48410 :: uu____48412  in
      uu____48404 :: uu____48406  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____48459 =
         let uu____48462 = lowercase_module_name full_filename  in
         namespace_of_module uu____48462  in
       match uu____48459 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____48501 -> d = d'
  
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
        let uu____48541 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____48541
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____48576 =
             let uu____48577 = is_interface filename  in
             if uu____48577
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____48699 =
               let uu____48701 =
                 let uu____48703 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____48703  in
               Prims.op_Negation uu____48701  in
             if uu____48699
             then
               let uu____48730 =
                 let uu____48733 = FStar_ST.op_Bang deps1  in d ::
                   uu____48733
                  in
               FStar_ST.op_Colon_Equals deps1 uu____48730
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____48830 =
               resolve_module_name original_or_working_map key  in
             match uu____48830 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____48840 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____48840
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____48846 -> false  in
           let record_open_module let_open lid =
             let uu____48865 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____48865
             then true
             else
               (if let_open
                then
                  (let uu____48874 = FStar_Ident.range_of_lid lid  in
                   let uu____48875 =
                     let uu____48881 =
                       let uu____48883 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____48883
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____48881)
                      in
                   FStar_Errors.log_issue uu____48874 uu____48875)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____48903 = FStar_Ident.range_of_lid lid  in
               let uu____48904 =
                 let uu____48910 =
                   let uu____48912 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____48912
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____48910)
                  in
               FStar_Errors.log_issue uu____48903 uu____48904
             else ()  in
           let record_open let_open lid =
             let uu____48932 = record_open_module let_open lid  in
             if uu____48932
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____48949 =
             match uu____48949 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____48956 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____48973 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____48973  in
             let alias = lowercase_join_longident lid true  in
             let uu____48978 = FStar_Util.smap_try_find original_map alias
                in
             match uu____48978 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____49046 = FStar_Ident.range_of_lid lid  in
                   let uu____49047 =
                     let uu____49053 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____49053)
                      in
                   FStar_Errors.log_issue uu____49046 uu____49047);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____49064 = add_dependence_edge working_map module_name
                in
             if uu____49064
             then ()
             else
               (let uu____49069 = FStar_Options.debug_any ()  in
                if uu____49069
                then
                  let uu____49072 = FStar_Ident.range_of_lid module_name  in
                  let uu____49073 =
                    let uu____49079 =
                      let uu____49081 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____49081
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____49079)
                     in
                  FStar_Errors.log_issue uu____49072 uu____49073
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____49093 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_49221 =
              match uu___426_49221 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49232 =
                        let uu____49234 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49234
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____49240) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49251 =
                        let uu____49253 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49253
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
                  let uu____49275 =
                    let uu____49276 = lowercase_join_longident lid true  in
                    FriendImplementation uu____49276  in
                  add_dep deps uu____49275
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____49281 = record_module_alias ident lid  in
                  if uu____49281
                  then
                    let uu____49284 =
                      let uu____49285 = lowercase_join_longident lid true  in
                      dep_edge uu____49285  in
                    add_dep deps uu____49284
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____49290,patterms) ->
                  FStar_List.iter
                    (fun uu____49312  ->
                       match uu____49312 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____49321,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____49327,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49329;
                    FStar_Parser_AST.mdest = uu____49330;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49332;
                    FStar_Parser_AST.mdest = uu____49333;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____49335,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49337;
                    FStar_Parser_AST.mdest = uu____49338;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____49342,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____49381  ->
                           match uu____49381 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____49394,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____49401 -> ()
              | FStar_Parser_AST.Pragma uu____49402 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____49405 =
                      let uu____49407 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____49407 > (Prims.parse_int "1")  in
                    if uu____49405
                    then
                      let uu____49432 =
                        let uu____49438 =
                          let uu____49440 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____49440
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____49438)
                         in
                      let uu____49445 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____49432 uu____49445
                    else ()))
            
            and collect_tycon uu___427_49448 =
              match uu___427_49448 with
              | FStar_Parser_AST.TyconAbstract (uu____49449,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____49461,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____49475,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49521  ->
                        match uu____49521 with
                        | (uu____49530,t,uu____49532) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____49537,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49599  ->
                        match uu____49599 with
                        | (uu____49613,t,uu____49615,uu____49616) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_49627 =
              match uu___428_49627 with
              | FStar_Parser_AST.DefineEffect (uu____49628,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____49642,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____49655,t);
                   FStar_Parser_AST.brange = uu____49657;
                   FStar_Parser_AST.blevel = uu____49658;
                   FStar_Parser_AST.aqual = uu____49659;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____49662,t);
                   FStar_Parser_AST.brange = uu____49664;
                   FStar_Parser_AST.blevel = uu____49665;
                   FStar_Parser_AST.aqual = uu____49666;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____49670;
                   FStar_Parser_AST.blevel = uu____49671;
                   FStar_Parser_AST.aqual = uu____49672;_} -> collect_term t
               | uu____49675 -> ())
            
            and collect_aqual uu___429_49676 =
              match uu___429_49676 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____49680 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_49684 =
              match uu___430_49684 with
              | FStar_Const.Const_int
                  (uu____49685,FStar_Pervasives_Native.Some
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
                  let uu____49712 =
                    let uu____49713 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____49713  in
                  add_dep deps uu____49712
              | FStar_Const.Const_char uu____49716 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____49719 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____49721 -> ()
            
            and collect_term' uu___433_49722 =
              match uu___433_49722 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____49731 =
                      let uu____49733 = FStar_Ident.text_of_id s  in
                      uu____49733 = "@"  in
                    if uu____49731
                    then
                      let uu____49738 =
                        let uu____49739 =
                          let uu____49740 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____49740
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____49739  in
                      collect_term' uu____49738
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____49744 -> ()
              | FStar_Parser_AST.Uvar uu____49745 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____49748) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____49773  ->
                        match uu____49773 with
                        | (t,uu____49779) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____49789) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____49791,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____49841  ->
                        match uu____49841 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____49870 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____49880,t1,t2) ->
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
                     (fun uu____49976  ->
                        match uu____49976 with
                        | (uu____49981,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____49984) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_50013  ->
                        match uu___431_50013 with
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
              | FStar_Parser_AST.NamedTyp (uu____50061,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____50065) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____50073) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____50081,uu____50082) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____50088) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____50102 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____50102);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_50112  ->
                        match uu___432_50112 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_50122 =
              match uu___434_50122 with
              | FStar_Parser_AST.PatVar (uu____50123,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____50129,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____50138 -> ()
              | FStar_Parser_AST.PatConst uu____50139 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____50147 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____50155) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____50176  ->
                       match uu____50176 with
                       | (uu____50181,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____50226 =
              match uu____50226 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____50244 = FStar_Parser_Driver.parse_file filename  in
            match uu____50244 with
            | (ast,uu____50257) ->
                let mname = lowercase_module_name filename  in
                ((let uu____50275 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____50275
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____50281 = FStar_ST.op_Bang deps  in
                  let uu____50307 = FStar_ST.op_Bang mo_roots  in
                  let uu____50333 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____50281;
                    additional_roots = uu____50307;
                    has_inline_for_extraction = uu____50333
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____50372 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____50372 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____50494 = dep_graph  in
    match uu____50494 with
    | Deps g -> let uu____50498 = FStar_Util.smap_copy g  in Deps uu____50498
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____50643 filename =
              match uu____50643 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____50684 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____50684  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____50715 = FStar_Options.debug_any ()  in
                         if uu____50715
                         then
                           let uu____50718 =
                             let uu____50720 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____50720  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____50718
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1257_50731 = dep_node  in
                           { edges = (uu___1257_50731.edges); color = Gray });
                        (let uu____50732 =
                           let uu____50743 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____50743
                            in
                         match uu____50732 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1263_50779 = dep_node  in
                                 {
                                   edges = (uu___1263_50779.edges);
                                   color = Black
                                 });
                              (let uu____50781 = FStar_Options.debug_any ()
                                  in
                               if uu____50781
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____50787 =
                                 let uu____50791 =
                                   FStar_List.collect
                                     (fun uu___435_50798  ->
                                        match uu___435_50798 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____50791 all_friends1
                                  in
                               (uu____50787, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____50864 = FStar_Options.debug_any ()  in
             if uu____50864
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____50893 = deps  in
               match uu____50893 with
               | Deps dg ->
                   let uu____50897 = deps_empty ()  in
                   (match uu____50897 with
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
                                  | uu____50947 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____50955  ->
                                  let uu____50957 =
                                    let uu___1298_50958 = dep_node  in
                                    let uu____50959 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____50959; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____50957) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____50961 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____50961
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____50966 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____50966 with
             | (friends,all_files_0) ->
                 ((let uu____51009 = FStar_Options.debug_any ()  in
                   if uu____51009
                   then
                     let uu____51012 =
                       let uu____51014 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____51014  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____51012
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____51033 =
                     (let uu____51045 = FStar_Options.debug_any ()  in
                      if uu____51045
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____51033 with
                   | (uu____51068,all_files) ->
                       ((let uu____51083 = FStar_Options.debug_any ()  in
                         if uu____51083
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____51090 = FStar_ST.op_Bang widened  in
                         (all_files, uu____51090))))))
  
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
                let uu____51176 = FStar_Options.find_file fn  in
                match uu____51176 with
                | FStar_Pervasives_Native.None  ->
                    let uu____51182 =
                      let uu____51188 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____51188)
                       in
                    FStar_Errors.raise_err uu____51182
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____51218 =
          let uu____51222 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____51222  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____51218  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____51289 =
          let uu____51291 = deps_try_find dep_graph file_name  in
          uu____51291 = FStar_Pervasives_Native.None  in
        if uu____51289
        then
          let uu____51297 =
            let uu____51309 =
              let uu____51323 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____51323 file_name  in
            match uu____51309 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____51297 with
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
                  let uu____51467 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____51467
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____51475 = FStar_List.unique deps1  in
                  { edges = uu____51475; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____51477 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____51477)))
        else ()  in
      FStar_Options.profile
        (fun uu____51487  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____51490  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____51522 =
            let uu____51528 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____51528)  in
          FStar_Errors.raise_err uu____51522)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____51565 = deps_try_find dep_graph1 filename  in
             match uu____51565 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____51569 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____51569
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____51583 =
                           implementation_of file_system_map f  in
                         (match uu____51583 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51594 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____51600 =
                           implementation_of file_system_map f  in
                         (match uu____51600 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51611 -> [x; UseImplementation f])
                     | uu____51615 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1384_51618 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____51620 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____51620);
                deps_add_dep dep_graph1 filename
                  (let uu___1389_51630 = node  in
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
        let uu____51674 =
          FStar_Options.profile
            (fun uu____51693  ->
               let uu____51694 =
                 let uu____51696 = FStar_Options.codegen ()  in
                 uu____51696 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____51694)
            (fun uu____51702  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____51674 with
        | (all_files,uu____51720) ->
            ((let uu____51730 = FStar_Options.debug_any ()  in
              if uu____51730
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
  
let (hash_dependences :
  deps ->
    Prims.string ->
      Prims.string ->
        (Prims.string,(Prims.string * Prims.string) Prims.list)
          FStar_Util.either)
  =
  fun deps  ->
    fun fn  ->
      fun cache_file  ->
        let file_system_map = deps.file_system_map  in
        let all_cmd_line_files = deps.cmd_line_files  in
        let deps1 = deps.dep_graph  in
        let fn1 =
          let uu____51800 = FStar_Options.find_file fn  in
          match uu____51800 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____51808 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____51822 = FStar_Options.debug_any ()  in
           if uu____51822
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____51841 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____51841
          then
            let uu____51852 =
              let uu____51859 =
                let uu____51861 =
                  let uu____51863 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____51863  in
                digest_of_file1 uu____51861  in
              ("interface", uu____51859)  in
            [uu____51852]
          else []  in
        let binary_deps =
          let uu____51895 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____51895
            (FStar_List.filter
               (fun fn2  ->
                  let uu____51910 =
                    (is_interface fn2) &&
                      (let uu____51913 = lowercase_module_name fn2  in
                       uu____51913 = module_name)
                     in
                  Prims.op_Negation uu____51910))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____51929 = lowercase_module_name fn11  in
                 let uu____51931 = lowercase_module_name fn2  in
                 FStar_String.compare uu____51929 uu____51931) binary_deps
           in
        let rec hash_deps out uu___436_51967 =
          match uu___436_51967 with
          | [] ->
              FStar_Util.Inr
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____52034 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____52034
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____52055 = FStar_Options.debug_any ()  in
                     if uu____52055
                     then
                       let uu____52058 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____52058
                     else ());
                    (let uu____52063 =
                       FStar_Util.format1 "cache file %s does not exist"
                         cache_fn
                        in
                     FStar_Util.Inl uu____52063))
               | FStar_Pervasives_Native.Some dig ->
                   let uu____52078 =
                     let uu____52087 =
                       let uu____52094 = lowercase_module_name fn2  in
                       (uu____52094, dig)  in
                     uu____52087 :: out  in
                   hash_deps uu____52078 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____52134 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____52160  ->
              match uu____52160 with
              | (m,d) ->
                  let uu____52174 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____52174))
       in
    FStar_All.pipe_right uu____52134 (FStar_String.concat "\n")
  
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
              let uu____52209 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____52209 FStar_Option.get  in
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
    let uu____52238 = deps.dep_graph  in
    match uu____52238 with
    | Deps deps1 ->
        let uu____52242 =
          let uu____52244 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____52262 =
                       let uu____52264 =
                         let uu____52266 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____52266
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____52264
                        in
                     uu____52262 :: out) []
             in
          FStar_All.pipe_right uu____52244 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____52242 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____52338 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____52338) ||
          (let uu____52345 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____52345)
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
            let uu____52388 =
              let uu____52392 = FStar_ST.op_Bang order  in ml_file ::
                uu____52392
               in
            FStar_ST.op_Colon_Equals order uu____52388
         in
      let rec aux uu___437_52455 =
        match uu___437_52455 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____52483 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____52483 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____52486 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____52486
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____52490;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____52499 = should_visit lc_module_name  in
              if uu____52499
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____52507 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____52507);
                 (let uu____52512 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____52512);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____52524 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____52524)
       in
    let sb =
      let uu____52555 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____52555  in
    let pr str =
      let uu____52565 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____52565  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____52618 =
          let uu____52620 =
            let uu____52624 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____52624  in
          FStar_Option.get uu____52620  in
        FStar_Util.replace_chars uu____52618 46 "_"  in
      let uu____52629 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____52629  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____52651 = output_file ".ml" f  in norm_path uu____52651  in
    let output_krml_file f =
      let uu____52663 = output_file ".krml" f  in norm_path uu____52663  in
    let output_cmx_file f =
      let uu____52675 = output_file ".cmx" f  in norm_path uu____52675  in
    let cache_file f =
      let uu____52687 = cache_file_name f  in norm_path uu____52687  in
    let all_checked_files =
      FStar_All.pipe_right keys
        (FStar_List.fold_left
           (fun all_checked_files  ->
              fun file_name  ->
                let process_one_key uu____52720 =
                  let dep_node =
                    let uu____52722 = deps_try_find deps.dep_graph file_name
                       in
                    FStar_All.pipe_right uu____52722 FStar_Option.get  in
                  let iface_deps =
                    let uu____52732 = is_interface file_name  in
                    if uu____52732
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____52743 =
                         let uu____52747 = lowercase_module_name file_name
                            in
                         interface_of deps.file_system_map uu____52747  in
                       match uu____52743 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some iface ->
                           let uu____52759 =
                             let uu____52762 =
                               let uu____52763 =
                                 deps_try_find deps.dep_graph iface  in
                               FStar_Option.get uu____52763  in
                             uu____52762.edges  in
                           FStar_Pervasives_Native.Some uu____52759)
                     in
                  let iface_deps1 =
                    FStar_Util.map_opt iface_deps
                      (FStar_List.filter
                         (fun iface_dep  ->
                            let uu____52780 =
                              FStar_Util.for_some (dep_subsumed_by iface_dep)
                                dep_node.edges
                               in
                            Prims.op_Negation uu____52780))
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
                      (fun uu____52840  ->
                         FStar_String.concat "\\\n\t" files3)
                      (fun uu____52843  ->
                         "Dependence analysis: concat files")
                     in
                  let cache_file_name1 = cache_file file_name  in
                  let all_checked_files1 =
                    let uu____52852 =
                      let uu____52854 =
                        let uu____52856 = module_name_of_file file_name  in
                        FStar_Options.should_be_already_cached uu____52856
                         in
                      Prims.op_Negation uu____52854  in
                    if uu____52852
                    then
                      (print_entry cache_file_name1 norm_f files4;
                       cache_file_name1
                       ::
                       all_checked_files)
                    else all_checked_files  in
                  let uu____52866 =
                    let uu____52875 = FStar_Options.cmi ()  in
                    if uu____52875
                    then
                      FStar_Options.profile
                        (fun uu____52895  ->
                           topological_dependences_of deps.file_system_map
                             deps.dep_graph deps.interfaces_with_inlining
                             [file_name] true)
                        (fun uu____52900  ->
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
                       let uu____52944 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           (FStar_List.append fst_files fst_files_from_iface)
                          in
                       (uu____52944, false))
                     in
                  match uu____52866 with
                  | (all_fst_files_dep,widened) ->
                      let all_checked_fst_dep_files =
                        FStar_All.pipe_right all_fst_files_dep
                          (FStar_List.map cache_file)
                         in
                      let all_checked_fst_dep_files_string =
                        FStar_String.concat " \\\n\t"
                          all_checked_fst_dep_files
                         in
                      ((let uu____52991 = is_implementation file_name  in
                        if uu____52991
                        then
                          ((let uu____52995 =
                              (FStar_Options.cmi ()) && widened  in
                            if uu____52995
                            then
                              ((let uu____52999 = output_ml_file file_name
                                   in
                                print_entry uu____52999 cache_file_name1
                                  all_checked_fst_dep_files_string);
                               (let uu____53001 = output_krml_file file_name
                                   in
                                print_entry uu____53001 cache_file_name1
                                  all_checked_fst_dep_files_string))
                            else
                              ((let uu____53006 = output_ml_file file_name
                                   in
                                print_entry uu____53006 cache_file_name1 "");
                               (let uu____53009 = output_krml_file file_name
                                   in
                                print_entry uu____53009 cache_file_name1 "")));
                           (let cmx_files =
                              let extracted_fst_files =
                                FStar_All.pipe_right all_fst_files_dep
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____53034 =
                                           lowercase_module_name df  in
                                         let uu____53036 =
                                           lowercase_module_name file_name
                                            in
                                         uu____53034 <> uu____53036) &&
                                          (let uu____53040 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____53040)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            let uu____53050 =
                              let uu____53052 =
                                lowercase_module_name file_name  in
                              FStar_Options.should_extract uu____53052  in
                            if uu____53050
                            then
                              let cmx_files1 =
                                FStar_String.concat "\\\n\t" cmx_files  in
                              let uu____53058 = output_cmx_file file_name  in
                              let uu____53060 = output_ml_file file_name  in
                              print_entry uu____53058 uu____53060 cmx_files1
                            else ()))
                        else
                          (let uu____53066 =
                             (let uu____53070 =
                                let uu____53072 =
                                  lowercase_module_name file_name  in
                                has_implementation deps.file_system_map
                                  uu____53072
                                 in
                              Prims.op_Negation uu____53070) &&
                               (is_interface file_name)
                              in
                           if uu____53066
                           then
                             let uu____53075 =
                               (FStar_Options.cmi ()) && (widened || true)
                                in
                             (if uu____53075
                              then
                                let uu____53079 = output_krml_file file_name
                                   in
                                print_entry uu____53079 cache_file_name1
                                  all_checked_fst_dep_files_string
                              else
                                (let uu____53083 = output_krml_file file_name
                                    in
                                 print_entry uu____53083 cache_file_name1 ""))
                           else ()));
                       all_checked_files1)
                   in
                FStar_Options.profile process_one_key
                  (fun uu____53092  ->
                     FStar_Util.format1 "Dependence analysis: output key %s"
                       file_name)) [])
       in
    let all_fst_files =
      let uu____53102 =
        FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
      FStar_All.pipe_right uu____53102
        (FStar_Util.sort_with FStar_String.compare)
       in
    let all_ml_files =
      let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right all_fst_files
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____53143 = FStar_Options.should_extract mname  in
              if uu____53143
              then
                let uu____53146 = output_ml_file fst_file  in
                FStar_Util.smap_add ml_file_map mname uu____53146
              else ()));
      sort_output_files ml_file_map  in
    let all_krml_files =
      let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____53173 = output_krml_file fst_file  in
              FStar_Util.smap_add krml_file_map mname uu____53173));
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
    let uu____53221 = FStar_Options.dep ()  in
    match uu____53221 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____53230  -> print_full deps)
          (fun uu____53232  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____53238 ->
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
         fun uu____53293  ->
           fun s  ->
             match uu____53293 with
             | (v0,v1) ->
                 let uu____53322 =
                   let uu____53324 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____53324  in
                 FStar_String.op_Hat s uu____53322) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____53345 =
        let uu____53347 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53347  in
      has_interface deps.file_system_map uu____53345
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____53363 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53363  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____53374 =
                   let uu____53376 = module_name_of_file f  in
                   FStar_String.lowercase uu____53376  in
                 uu____53374 = m)))
  