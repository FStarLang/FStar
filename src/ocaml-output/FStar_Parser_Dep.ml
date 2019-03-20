open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____45975 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____45986 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____45997 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____46020 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____46031 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____46042 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____46053 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____46064 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____46112 =
             (l > lext) &&
               (let uu____46115 = FStar_String.substring f (l - lext) lext
                   in
                uu____46115 = ext)
              in
           if uu____46112
           then
             let uu____46122 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____46122
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____46129 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____46129 with
    | (FStar_Pervasives_Native.Some m)::uu____46143 ->
        FStar_Pervasives_Native.Some m
    | uu____46155 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46172 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____46172 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46186 = is_interface f  in Prims.op_Negation uu____46186
  
let list_of_option :
  'Auu____46193 .
    'Auu____46193 FStar_Pervasives_Native.option -> 'Auu____46193 Prims.list
  =
  fun uu___423_46202  ->
    match uu___423_46202 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____46211 .
    ('Auu____46211 FStar_Pervasives_Native.option * 'Auu____46211
      FStar_Pervasives_Native.option) -> 'Auu____46211 Prims.list
  =
  fun uu____46226  ->
    match uu____46226 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46254 =
      let uu____46258 = FStar_Util.basename f  in
      check_and_strip_suffix uu____46258  in
    match uu____46254 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____46265 =
          let uu____46271 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____46271)  in
        FStar_Errors.raise_err uu____46265
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46285 = module_name_of_file f  in
    FStar_String.lowercase uu____46285
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____46298 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____46298 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____46301 ->
        let uu____46304 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____46304
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____46344 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____46367 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____46390 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____46413 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_46431  ->
    match uu___424_46431 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____46450 . unit -> 'Auu____46450 Prims.list =
  fun uu____46453  -> [] 
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
  fun uu____46795  ->
    fun k  -> match uu____46795 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____46817  ->
    fun k  ->
      fun v1  ->
        match uu____46817 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____46832  ->
    match uu____46832 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____46844  ->
    let uu____46845 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____46845
  
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
  let uu____46903 = deps_empty ()  in
  let uu____46904 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____46916 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____46903 uu____46904 [] [] [] uu____46916 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_46929  ->
    match uu___425_46929 with
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
      let uu____46958 = FStar_Util.smap_try_find file_system_map key  in
      match uu____46958 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____46985) ->
          let uu____47007 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____47007
      | FStar_Pervasives_Native.Some
          (uu____47010,FStar_Pervasives_Native.Some fn) ->
          let uu____47033 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____47033
      | uu____47036 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47069 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47069 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____47096) ->
          FStar_Pervasives_Native.Some iface
      | uu____47119 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47152 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47152 with
      | FStar_Pervasives_Native.Some
          (uu____47178,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____47202 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____47231 = interface_of file_system_map key  in
      FStar_Option.isSome uu____47231
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47251 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____47251
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____47286 =
      let uu____47290 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____47290  in
    match uu____47286 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____47301 =
            (let uu____47305 = FStar_Options.should_be_already_cached mname
                in
             Prims.op_Negation uu____47305) &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____47308 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____47308))
             in
          if uu____47301
          then
            let uu____47311 =
              let uu____47317 =
                let uu____47319 = FStar_Options.prepend_cache_dir cache_fn
                   in
                FStar_Util.format3
                  "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____47319
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____47317)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____47311
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____47326 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____47326
        then
          let uu____47332 =
            let uu____47338 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____47338)
             in
          FStar_Errors.raise_err uu____47332
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____47374 = FStar_Util.smap_try_find memo x  in
    match uu____47374 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____47401 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____47401 FStar_Util.must
  
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
                      (let uu____47455 = lowercase_module_name fn  in
                       key = uu____47455)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____47474 = interface_of file_system_map key  in
              (match uu____47474 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47481 =
                     let uu____47487 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____47487)  in
                   FStar_Errors.raise_err uu____47481
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____47497 =
                (cmd_line_has_impl key) &&
                  (let uu____47500 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____47500)
                 in
              if uu____47497
              then
                let uu____47507 = FStar_Options.expose_interfaces ()  in
                (if uu____47507
                 then
                   let uu____47511 =
                     let uu____47513 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____47513  in
                   maybe_use_cache_of uu____47511
                 else
                   (let uu____47520 =
                      let uu____47526 =
                        let uu____47528 =
                          let uu____47530 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____47530  in
                        let uu____47535 =
                          let uu____47537 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____47537  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____47528 uu____47535
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____47526)
                       in
                    FStar_Errors.raise_err uu____47520))
              else
                (let uu____47547 =
                   let uu____47549 = interface_of file_system_map key  in
                   FStar_Option.get uu____47549  in
                 maybe_use_cache_of uu____47547)
          | PreferInterface key ->
              let uu____47556 = implementation_of file_system_map key  in
              (match uu____47556 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47562 =
                     let uu____47568 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47568)
                      in
                   FStar_Errors.raise_err uu____47562
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____47578 = implementation_of file_system_map key  in
              (match uu____47578 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47584 =
                     let uu____47590 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47590)
                      in
                   FStar_Errors.raise_err uu____47584
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____47600 = implementation_of file_system_map key  in
              (match uu____47600 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47606 =
                     let uu____47612 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47612)
                      in
                   FStar_Errors.raise_err uu____47606
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
          let uu____47673 = deps_try_find deps fn  in
          match uu____47673 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____47681;_} ->
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
    (let uu____47695 =
       let uu____47697 =
         let uu____47699 =
           let uu____47701 =
             let uu____47705 =
               let uu____47709 = deps_keys graph  in
               FStar_List.unique uu____47709  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____47723 =
                      let uu____47724 = deps_try_find graph k  in
                      FStar_Util.must uu____47724  in
                    uu____47723.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____47745 =
                      let uu____47747 = lowercase_module_name k  in
                      r uu____47747  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____47745
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____47705
              in
           FStar_String.concat "\n" uu____47701  in
         FStar_String.op_Hat uu____47699 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____47697  in
     FStar_Util.write_file "dep.graph" uu____47695)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____47768  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____47794 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____47794  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____47834 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____47834
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____47871 =
              let uu____47877 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____47877)  in
            FStar_Errors.raise_err uu____47871)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____47940 = FStar_Util.smap_try_find map1 key  in
      match uu____47940 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____47987 = is_interface full_path  in
          if uu____47987
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____48036 = is_interface full_path  in
          if uu____48036
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____48078 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____48096  ->
          match uu____48096 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____48078);
    FStar_List.iter
      (fun f  ->
         let uu____48115 = lowercase_module_name f  in
         add_entry uu____48115 f) filenames;
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
        (let uu____48147 =
           let uu____48151 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____48151  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____48187 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____48187  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____48147);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____48307 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____48307 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____48330 = string_of_lid l last1  in
      FStar_String.lowercase uu____48330
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____48339 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____48339
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____48361 =
        let uu____48363 =
          let uu____48365 =
            let uu____48367 =
              let uu____48371 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____48371  in
            FStar_Util.must uu____48367  in
          FStar_String.lowercase uu____48365  in
        uu____48363 <> k'  in
      if uu____48361
      then
        let uu____48376 = FStar_Ident.range_of_lid lid  in
        let uu____48377 =
          let uu____48383 =
            let uu____48385 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____48385 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____48383)  in
        FStar_Errors.log_issue uu____48376 uu____48377
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____48401 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____48423 = FStar_Options.prims_basename ()  in
      let uu____48425 =
        let uu____48429 = FStar_Options.pervasives_basename ()  in
        let uu____48431 =
          let uu____48435 = FStar_Options.pervasives_native_basename ()  in
          [uu____48435]  in
        uu____48429 :: uu____48431  in
      uu____48423 :: uu____48425  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____48478 =
         let uu____48481 = lowercase_module_name full_filename  in
         namespace_of_module uu____48481  in
       match uu____48478 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____48520 -> d = d'
  
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
        let uu____48560 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____48560
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____48595 =
             let uu____48596 = is_interface filename  in
             if uu____48596
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____48718 =
               let uu____48720 =
                 let uu____48722 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____48722  in
               Prims.op_Negation uu____48720  in
             if uu____48718
             then
               let uu____48749 =
                 let uu____48752 = FStar_ST.op_Bang deps1  in d ::
                   uu____48752
                  in
               FStar_ST.op_Colon_Equals deps1 uu____48749
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____48849 =
               resolve_module_name original_or_working_map key  in
             match uu____48849 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____48859 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____48859
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____48865 -> false  in
           let record_open_module let_open lid =
             let uu____48884 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____48884
             then true
             else
               (if let_open
                then
                  (let uu____48893 = FStar_Ident.range_of_lid lid  in
                   let uu____48894 =
                     let uu____48900 =
                       let uu____48902 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____48902
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____48900)
                      in
                   FStar_Errors.log_issue uu____48893 uu____48894)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____48922 = FStar_Ident.range_of_lid lid  in
               let uu____48923 =
                 let uu____48929 =
                   let uu____48931 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____48931
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____48929)
                  in
               FStar_Errors.log_issue uu____48922 uu____48923
             else ()  in
           let record_open let_open lid =
             let uu____48951 = record_open_module let_open lid  in
             if uu____48951
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____48968 =
             match uu____48968 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____48975 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____48992 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____48992  in
             let alias = lowercase_join_longident lid true  in
             let uu____48997 = FStar_Util.smap_try_find original_map alias
                in
             match uu____48997 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____49065 = FStar_Ident.range_of_lid lid  in
                   let uu____49066 =
                     let uu____49072 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____49072)
                      in
                   FStar_Errors.log_issue uu____49065 uu____49066);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____49083 = add_dependence_edge working_map module_name
                in
             if uu____49083
             then ()
             else
               (let uu____49088 = FStar_Options.debug_any ()  in
                if uu____49088
                then
                  let uu____49091 = FStar_Ident.range_of_lid module_name  in
                  let uu____49092 =
                    let uu____49098 =
                      let uu____49100 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____49100
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____49098)
                     in
                  FStar_Errors.log_issue uu____49091 uu____49092
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____49112 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_49240 =
              match uu___426_49240 with
              | FStar_Parser_AST.Module (lid,decls) ->
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
              | FStar_Parser_AST.Interface (lid,decls,uu____49259) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49270 =
                        let uu____49272 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49272
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
                  let uu____49294 =
                    let uu____49295 = lowercase_join_longident lid true  in
                    FriendImplementation uu____49295  in
                  add_dep deps uu____49294
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____49300 = record_module_alias ident lid  in
                  if uu____49300
                  then
                    let uu____49303 =
                      let uu____49304 = lowercase_join_longident lid true  in
                      dep_edge uu____49304  in
                    add_dep deps uu____49303
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____49309,patterms) ->
                  FStar_List.iter
                    (fun uu____49331  ->
                       match uu____49331 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____49340,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____49346,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49348;
                    FStar_Parser_AST.mdest = uu____49349;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49351;
                    FStar_Parser_AST.mdest = uu____49352;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____49354,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49356;
                    FStar_Parser_AST.mdest = uu____49357;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____49361,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____49400  ->
                           match uu____49400 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____49413,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____49420 -> ()
              | FStar_Parser_AST.Pragma uu____49421 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____49424 =
                      let uu____49426 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____49426 > (Prims.parse_int "1")  in
                    if uu____49424
                    then
                      let uu____49451 =
                        let uu____49457 =
                          let uu____49459 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____49459
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____49457)
                         in
                      let uu____49464 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____49451 uu____49464
                    else ()))
            
            and collect_tycon uu___427_49467 =
              match uu___427_49467 with
              | FStar_Parser_AST.TyconAbstract (uu____49468,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____49480,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____49494,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49540  ->
                        match uu____49540 with
                        | (uu____49549,t,uu____49551) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____49556,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49618  ->
                        match uu____49618 with
                        | (uu____49632,t,uu____49634,uu____49635) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_49646 =
              match uu___428_49646 with
              | FStar_Parser_AST.DefineEffect (uu____49647,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____49661,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____49674,t);
                   FStar_Parser_AST.brange = uu____49676;
                   FStar_Parser_AST.blevel = uu____49677;
                   FStar_Parser_AST.aqual = uu____49678;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____49681,t);
                   FStar_Parser_AST.brange = uu____49683;
                   FStar_Parser_AST.blevel = uu____49684;
                   FStar_Parser_AST.aqual = uu____49685;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____49689;
                   FStar_Parser_AST.blevel = uu____49690;
                   FStar_Parser_AST.aqual = uu____49691;_} -> collect_term t
               | uu____49694 -> ())
            
            and collect_aqual uu___429_49695 =
              match uu___429_49695 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____49699 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_49703 =
              match uu___430_49703 with
              | FStar_Const.Const_int
                  (uu____49704,FStar_Pervasives_Native.Some
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
                  let uu____49731 =
                    let uu____49732 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____49732  in
                  add_dep deps uu____49731
              | FStar_Const.Const_char uu____49735 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____49738 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____49740 -> ()
            
            and collect_term' uu___433_49741 =
              match uu___433_49741 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____49750 =
                      let uu____49752 = FStar_Ident.text_of_id s  in
                      uu____49752 = "@"  in
                    if uu____49750
                    then
                      let uu____49757 =
                        let uu____49758 =
                          let uu____49759 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____49759
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____49758  in
                      collect_term' uu____49757
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____49763 -> ()
              | FStar_Parser_AST.Uvar uu____49764 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____49767) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____49792  ->
                        match uu____49792 with
                        | (t,uu____49798) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____49808) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____49810,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____49860  ->
                        match uu____49860 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____49889 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____49899,t1,t2) ->
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
                     (fun uu____49995  ->
                        match uu____49995 with
                        | (uu____50000,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____50003) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_50032  ->
                        match uu___431_50032 with
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
              | FStar_Parser_AST.NamedTyp (uu____50080,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____50084) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____50092) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____50100,uu____50101) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____50107) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____50121 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____50121);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_50131  ->
                        match uu___432_50131 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_50141 =
              match uu___434_50141 with
              | FStar_Parser_AST.PatVar (uu____50142,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____50148,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____50157 -> ()
              | FStar_Parser_AST.PatConst uu____50158 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____50166 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____50174) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____50195  ->
                       match uu____50195 with
                       | (uu____50200,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____50245 =
              match uu____50245 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____50263 = FStar_Parser_Driver.parse_file filename  in
            match uu____50263 with
            | (ast,uu____50276) ->
                let mname = lowercase_module_name filename  in
                ((let uu____50294 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____50294
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____50300 = FStar_ST.op_Bang deps  in
                  let uu____50326 = FStar_ST.op_Bang mo_roots  in
                  let uu____50352 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____50300;
                    additional_roots = uu____50326;
                    has_inline_for_extraction = uu____50352
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____50391 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____50391 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____50513 = dep_graph  in
    match uu____50513 with
    | Deps g -> let uu____50517 = FStar_Util.smap_copy g  in Deps uu____50517
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____50662 filename =
              match uu____50662 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____50703 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____50703  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____50734 = FStar_Options.debug_any ()  in
                         if uu____50734
                         then
                           let uu____50737 =
                             let uu____50739 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____50739  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____50737
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1258_50750 = dep_node  in
                           { edges = (uu___1258_50750.edges); color = Gray });
                        (let uu____50751 =
                           let uu____50762 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____50762
                            in
                         match uu____50751 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1264_50798 = dep_node  in
                                 {
                                   edges = (uu___1264_50798.edges);
                                   color = Black
                                 });
                              (let uu____50800 = FStar_Options.debug_any ()
                                  in
                               if uu____50800
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____50806 =
                                 let uu____50810 =
                                   FStar_List.collect
                                     (fun uu___435_50817  ->
                                        match uu___435_50817 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____50810 all_friends1
                                  in
                               (uu____50806, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____50883 = FStar_Options.debug_any ()  in
             if uu____50883
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____50912 = deps  in
               match uu____50912 with
               | Deps dg ->
                   let uu____50916 = deps_empty ()  in
                   (match uu____50916 with
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
                                  | uu____50966 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____50974  ->
                                  let uu____50976 =
                                    let uu___1299_50977 = dep_node  in
                                    let uu____50978 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____50978; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____50976) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____50980 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____50980
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____50985 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____50985 with
             | (friends,all_files_0) ->
                 ((let uu____51028 = FStar_Options.debug_any ()  in
                   if uu____51028
                   then
                     let uu____51031 =
                       let uu____51033 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____51033  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____51031
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____51052 =
                     (let uu____51064 = FStar_Options.debug_any ()  in
                      if uu____51064
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____51052 with
                   | (uu____51087,all_files) ->
                       ((let uu____51102 = FStar_Options.debug_any ()  in
                         if uu____51102
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____51109 = FStar_ST.op_Bang widened  in
                         (all_files, uu____51109))))))
  
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
                let uu____51195 = FStar_Options.find_file fn  in
                match uu____51195 with
                | FStar_Pervasives_Native.None  ->
                    let uu____51201 =
                      let uu____51207 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____51207)
                       in
                    FStar_Errors.raise_err uu____51201
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____51237 =
          let uu____51241 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____51241  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____51237  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____51308 =
          let uu____51310 = deps_try_find dep_graph file_name  in
          uu____51310 = FStar_Pervasives_Native.None  in
        if uu____51308
        then
          let uu____51316 =
            let uu____51328 =
              let uu____51342 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____51342 file_name  in
            match uu____51328 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____51316 with
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
                  let uu____51486 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____51486
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____51494 = FStar_List.unique deps1  in
                  { edges = uu____51494; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____51496 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____51496)))
        else ()  in
      FStar_Options.profile
        (fun uu____51506  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____51509  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____51541 =
            let uu____51547 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____51547)  in
          FStar_Errors.raise_err uu____51541)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____51584 = deps_try_find dep_graph1 filename  in
             match uu____51584 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____51588 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____51588
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____51602 =
                           implementation_of file_system_map f  in
                         (match uu____51602 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51613 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____51619 =
                           implementation_of file_system_map f  in
                         (match uu____51619 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51630 -> [x; UseImplementation f])
                     | uu____51634 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1385_51637 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____51639 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____51639);
                deps_add_dep dep_graph1 filename
                  (let uu___1390_51649 = node  in
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
        let uu____51693 =
          FStar_Options.profile
            (fun uu____51712  ->
               let uu____51713 =
                 let uu____51715 = FStar_Options.codegen ()  in
                 uu____51715 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____51713)
            (fun uu____51721  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____51693 with
        | (all_files,uu____51739) ->
            ((let uu____51749 = FStar_Options.debug_any ()  in
              if uu____51749
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
          let uu____51819 = FStar_Options.find_file fn  in
          match uu____51819 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____51827 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____51841 = FStar_Options.debug_any ()  in
           if uu____51841
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____51860 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____51860
          then
            let uu____51871 =
              let uu____51878 =
                let uu____51880 =
                  let uu____51882 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____51882  in
                digest_of_file1 uu____51880  in
              ("interface", uu____51878)  in
            [uu____51871]
          else []  in
        let binary_deps =
          let uu____51914 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____51914
            (FStar_List.filter
               (fun fn2  ->
                  let uu____51929 =
                    (is_interface fn2) &&
                      (let uu____51932 = lowercase_module_name fn2  in
                       uu____51932 = module_name)
                     in
                  Prims.op_Negation uu____51929))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____51948 = lowercase_module_name fn11  in
                 let uu____51950 = lowercase_module_name fn2  in
                 FStar_String.compare uu____51948 uu____51950) binary_deps
           in
        let rec hash_deps out uu___436_51986 =
          match uu___436_51986 with
          | [] ->
              FStar_Util.Inr
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____52053 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____52053
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____52074 = FStar_Options.debug_any ()  in
                     if uu____52074
                     then
                       let uu____52077 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____52077
                     else ());
                    (let uu____52082 =
                       FStar_Util.format1 "cache file %s does not exist"
                         cache_fn
                        in
                     FStar_Util.Inl uu____52082))
               | FStar_Pervasives_Native.Some dig ->
                   let uu____52097 =
                     let uu____52106 =
                       let uu____52113 = lowercase_module_name fn2  in
                       (uu____52113, dig)  in
                     uu____52106 :: out  in
                   hash_deps uu____52097 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____52153 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____52179  ->
              match uu____52179 with
              | (m,d) ->
                  let uu____52193 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____52193))
       in
    FStar_All.pipe_right uu____52153 (FStar_String.concat "\n")
  
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
              let uu____52228 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____52228 FStar_Option.get  in
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
    let uu____52257 = deps.dep_graph  in
    match uu____52257 with
    | Deps deps1 ->
        let uu____52261 =
          let uu____52263 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____52281 =
                       let uu____52283 =
                         let uu____52285 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____52285
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____52283
                        in
                     uu____52281 :: out) []
             in
          FStar_All.pipe_right uu____52263 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____52261 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____52357 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____52357) ||
          (let uu____52364 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____52364)
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
            let uu____52407 =
              let uu____52411 = FStar_ST.op_Bang order  in ml_file ::
                uu____52411
               in
            FStar_ST.op_Colon_Equals order uu____52407
         in
      let rec aux uu___437_52474 =
        match uu___437_52474 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____52502 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____52502 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____52505 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____52505
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____52509;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____52518 = should_visit lc_module_name  in
              if uu____52518
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____52526 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____52526);
                 (let uu____52531 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____52531);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____52543 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____52543)
       in
    let sb =
      let uu____52574 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____52574  in
    let pr str =
      let uu____52584 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____52584  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____52637 =
          let uu____52639 =
            let uu____52643 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____52643  in
          FStar_Option.get uu____52639  in
        FStar_Util.replace_chars uu____52637 46 "_"  in
      let uu____52648 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____52648  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____52670 = output_file ".ml" f  in norm_path uu____52670  in
    let output_krml_file f =
      let uu____52682 = output_file ".krml" f  in norm_path uu____52682  in
    let output_cmx_file f =
      let uu____52694 = output_file ".cmx" f  in norm_path uu____52694  in
    let cache_file f =
      let uu____52706 = cache_file_name f  in norm_path uu____52706  in
    let all_checked_files =
      FStar_All.pipe_right keys
        (FStar_List.fold_left
           (fun all_checked_files  ->
              fun file_name  ->
                let process_one_key uu____52739 =
                  let dep_node =
                    let uu____52741 = deps_try_find deps.dep_graph file_name
                       in
                    FStar_All.pipe_right uu____52741 FStar_Option.get  in
                  let iface_deps =
                    let uu____52751 = is_interface file_name  in
                    if uu____52751
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____52762 =
                         let uu____52766 = lowercase_module_name file_name
                            in
                         interface_of deps.file_system_map uu____52766  in
                       match uu____52762 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some iface ->
                           let uu____52778 =
                             let uu____52781 =
                               let uu____52782 =
                                 deps_try_find deps.dep_graph iface  in
                               FStar_Option.get uu____52782  in
                             uu____52781.edges  in
                           FStar_Pervasives_Native.Some uu____52778)
                     in
                  let iface_deps1 =
                    FStar_Util.map_opt iface_deps
                      (FStar_List.filter
                         (fun iface_dep  ->
                            let uu____52799 =
                              FStar_Util.for_some (dep_subsumed_by iface_dep)
                                dep_node.edges
                               in
                            Prims.op_Negation uu____52799))
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
                      (fun uu____52859  ->
                         FStar_String.concat "\\\n\t" files3)
                      (fun uu____52862  ->
                         "Dependence analysis: concat files")
                     in
                  let cache_file_name1 = cache_file file_name  in
                  let all_checked_files1 =
                    let uu____52871 =
                      let uu____52873 =
                        let uu____52875 = module_name_of_file file_name  in
                        FStar_Options.should_be_already_cached uu____52875
                         in
                      Prims.op_Negation uu____52873  in
                    if uu____52871
                    then
                      (print_entry cache_file_name1 norm_f files4;
                       cache_file_name1
                       ::
                       all_checked_files)
                    else all_checked_files  in
                  let uu____52885 =
                    let uu____52894 = FStar_Options.cmi ()  in
                    if uu____52894
                    then
                      FStar_Options.profile
                        (fun uu____52914  ->
                           topological_dependences_of deps.file_system_map
                             deps.dep_graph deps.interfaces_with_inlining
                             [file_name] true)
                        (fun uu____52919  ->
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
                       let uu____52963 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           (FStar_List.append fst_files fst_files_from_iface)
                          in
                       (uu____52963, false))
                     in
                  match uu____52885 with
                  | (all_fst_files_dep,widened) ->
                      let all_checked_fst_dep_files =
                        FStar_All.pipe_right all_fst_files_dep
                          (FStar_List.map cache_file)
                         in
                      let all_checked_fst_dep_files_string =
                        FStar_String.concat " \\\n\t"
                          all_checked_fst_dep_files
                         in
                      ((let uu____53010 = is_implementation file_name  in
                        if uu____53010
                        then
                          ((let uu____53014 =
                              (FStar_Options.cmi ()) && widened  in
                            if uu____53014
                            then
                              ((let uu____53018 = output_ml_file file_name
                                   in
                                print_entry uu____53018 cache_file_name1
                                  all_checked_fst_dep_files_string);
                               (let uu____53020 = output_krml_file file_name
                                   in
                                print_entry uu____53020 cache_file_name1
                                  all_checked_fst_dep_files_string))
                            else
                              ((let uu____53025 = output_ml_file file_name
                                   in
                                print_entry uu____53025 cache_file_name1 "");
                               (let uu____53028 = output_krml_file file_name
                                   in
                                print_entry uu____53028 cache_file_name1 "")));
                           (let cmx_files =
                              let extracted_fst_files =
                                FStar_All.pipe_right all_fst_files_dep
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____53053 =
                                           lowercase_module_name df  in
                                         let uu____53055 =
                                           lowercase_module_name file_name
                                            in
                                         uu____53053 <> uu____53055) &&
                                          (let uu____53059 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____53059)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            let uu____53069 =
                              let uu____53071 =
                                lowercase_module_name file_name  in
                              FStar_Options.should_extract uu____53071  in
                            if uu____53069
                            then
                              let cmx_files1 =
                                FStar_String.concat "\\\n\t" cmx_files  in
                              let uu____53077 = output_cmx_file file_name  in
                              let uu____53079 = output_ml_file file_name  in
                              print_entry uu____53077 uu____53079 cmx_files1
                            else ()))
                        else
                          (let uu____53085 =
                             (let uu____53089 =
                                let uu____53091 =
                                  lowercase_module_name file_name  in
                                has_implementation deps.file_system_map
                                  uu____53091
                                 in
                              Prims.op_Negation uu____53089) &&
                               (is_interface file_name)
                              in
                           if uu____53085
                           then
                             let uu____53094 =
                               (FStar_Options.cmi ()) && (widened || true)
                                in
                             (if uu____53094
                              then
                                let uu____53098 = output_krml_file file_name
                                   in
                                print_entry uu____53098 cache_file_name1
                                  all_checked_fst_dep_files_string
                              else
                                (let uu____53102 = output_krml_file file_name
                                    in
                                 print_entry uu____53102 cache_file_name1 ""))
                           else ()));
                       all_checked_files1)
                   in
                FStar_Options.profile process_one_key
                  (fun uu____53111  ->
                     FStar_Util.format1 "Dependence analysis: output key %s"
                       file_name)) [])
       in
    let all_fst_files =
      let uu____53121 =
        FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
      FStar_All.pipe_right uu____53121
        (FStar_Util.sort_with FStar_String.compare)
       in
    let all_ml_files =
      let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right all_fst_files
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____53162 = FStar_Options.should_extract mname  in
              if uu____53162
              then
                let uu____53165 = output_ml_file fst_file  in
                FStar_Util.smap_add ml_file_map mname uu____53165
              else ()));
      sort_output_files ml_file_map  in
    let all_krml_files =
      let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____53192 = output_krml_file fst_file  in
              FStar_Util.smap_add krml_file_map mname uu____53192));
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
    let uu____53240 = FStar_Options.dep ()  in
    match uu____53240 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____53249  -> print_full deps)
          (fun uu____53251  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____53257 ->
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
         fun uu____53312  ->
           fun s  ->
             match uu____53312 with
             | (v0,v1) ->
                 let uu____53341 =
                   let uu____53343 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____53343  in
                 FStar_String.op_Hat s uu____53341) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____53364 =
        let uu____53366 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53366  in
      has_interface deps.file_system_map uu____53364
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____53382 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53382  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____53393 =
                   let uu____53395 = module_name_of_file f  in
                   FStar_String.lowercase uu____53395  in
                 uu____53393 = m)))
  