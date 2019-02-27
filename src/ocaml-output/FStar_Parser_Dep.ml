open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____50493 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____50504 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____50515 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____50538 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____50549 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____50560 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____50571 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____50582 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____50630 =
             (l > lext) &&
               (let uu____50643 = FStar_String.substring f (l - lext) lext
                   in
                uu____50643 = ext)
              in
           if uu____50630
           then
             let uu____50664 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____50664
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____50681 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____50681 with
    | (FStar_Pervasives_Native.Some m)::uu____50695 ->
        FStar_Pervasives_Native.Some m
    | uu____50707 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____50724 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____50724 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____50738 = is_interface f  in Prims.op_Negation uu____50738
  
let list_of_option :
  'Auu____50745 .
    'Auu____50745 FStar_Pervasives_Native.option -> 'Auu____50745 Prims.list
  =
  fun uu___423_50754  ->
    match uu___423_50754 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____50763 .
    ('Auu____50763 FStar_Pervasives_Native.option * 'Auu____50763
      FStar_Pervasives_Native.option) -> 'Auu____50763 Prims.list
  =
  fun uu____50778  ->
    match uu____50778 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____50806 =
      let uu____50810 = FStar_Util.basename f  in
      check_and_strip_suffix uu____50810  in
    match uu____50806 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____50817 =
          let uu____50823 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____50823)  in
        FStar_Errors.raise_err uu____50817
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____50837 = module_name_of_file f  in
    FStar_String.lowercase uu____50837
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____50850 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____50850 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____50853 ->
        let uu____50856 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____50856
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____50898 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____50922 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____50946 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____50970 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_50989  ->
    match uu___424_50989 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____51008 . unit -> 'Auu____51008 Prims.list =
  fun uu____51011  -> [] 
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
  fun uu____51353  ->
    fun k  -> match uu____51353 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____51375  ->
    fun k  ->
      fun v1  ->
        match uu____51375 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____51390  ->
    match uu____51390 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____51402  ->
    let uu____51403 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____51403
  
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
  let uu____51461 = deps_empty ()  in
  let uu____51462 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____51474 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____51461 uu____51462 [] [] [] uu____51474 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_51487  ->
    match uu___425_51487 with
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
      let uu____51516 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51516 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____51543) ->
          let uu____51565 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____51565
      | FStar_Pervasives_Native.Some
          (uu____51568,FStar_Pervasives_Native.Some fn) ->
          let uu____51591 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____51591
      | uu____51594 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51627 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51627 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____51654) ->
          FStar_Pervasives_Native.Some iface
      | uu____51677 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51710 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51710 with
      | FStar_Pervasives_Native.Some
          (uu____51736,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____51760 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____51789 = interface_of file_system_map key  in
      FStar_Option.isSome uu____51789
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51809 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____51809
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____51836 =
        let uu____51838 = FStar_Options.lax ()  in
        if uu____51838 then ".checked.lax" else ".checked"  in
      FStar_String.op_Hat fn uu____51836  in
    let uu____51846 =
      let uu____51850 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____51850  in
    match uu____51846 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____51871 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____51871
        then
          let uu____51882 =
            let uu____51888 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____51888)
             in
          FStar_Errors.raise_err uu____51882
        else
          (let uu____51900 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____51900, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____51914 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____51914 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____51950 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____51950 FStar_Util.must
  
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
                      (let uu____52004 = lowercase_module_name fn  in
                       key = uu____52004)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____52023 = interface_of file_system_map key  in
              (match uu____52023 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52030 =
                     let uu____52036 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____52036)  in
                   FStar_Errors.raise_err uu____52030
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____52046 =
                (cmd_line_has_impl key) &&
                  (let uu____52049 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____52049)
                 in
              if uu____52046
              then
                let uu____52056 = FStar_Options.expose_interfaces ()  in
                (if uu____52056
                 then
                   let uu____52060 =
                     let uu____52062 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____52062  in
                   maybe_use_cache_of uu____52060
                 else
                   (let uu____52069 =
                      let uu____52075 =
                        let uu____52077 =
                          let uu____52079 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____52079  in
                        let uu____52084 =
                          let uu____52086 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____52086  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____52077 uu____52084
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____52075)
                       in
                    FStar_Errors.raise_err uu____52069))
              else
                (let uu____52096 =
                   let uu____52098 = interface_of file_system_map key  in
                   FStar_Option.get uu____52098  in
                 maybe_use_cache_of uu____52096)
          | PreferInterface key ->
              let uu____52105 = implementation_of file_system_map key  in
              (match uu____52105 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52111 =
                     let uu____52117 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52117)
                      in
                   FStar_Errors.raise_err uu____52111
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____52127 = implementation_of file_system_map key  in
              (match uu____52127 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52133 =
                     let uu____52139 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52139)
                      in
                   FStar_Errors.raise_err uu____52133
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____52149 = implementation_of file_system_map key  in
              (match uu____52149 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52155 =
                     let uu____52161 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52161)
                      in
                   FStar_Errors.raise_err uu____52155
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
          let uu____52222 = deps_try_find deps fn  in
          match uu____52222 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____52230;_} ->
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
    (let uu____52244 =
       let uu____52246 =
         let uu____52248 =
           let uu____52250 =
             let uu____52254 =
               let uu____52258 = deps_keys graph  in
               FStar_List.unique uu____52258  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____52272 =
                      let uu____52273 = deps_try_find graph k  in
                      FStar_Util.must uu____52273  in
                    uu____52272.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____52294 =
                      let uu____52296 = lowercase_module_name k  in
                      r uu____52296  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____52294
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____52254
              in
           FStar_String.concat "\n" uu____52250  in
         FStar_String.op_Hat uu____52248 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____52246  in
     FStar_Util.write_file "dep.graph" uu____52244)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____52317  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____52343 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____52343  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____52383 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____52383
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____52420 =
              let uu____52426 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____52426)  in
            FStar_Errors.raise_err uu____52420)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____52489 = FStar_Util.smap_try_find map1 key  in
      match uu____52489 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____52536 = is_interface full_path  in
          if uu____52536
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____52585 = is_interface full_path  in
          if uu____52585
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____52627 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____52645  ->
          match uu____52645 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____52627);
    FStar_List.iter
      (fun f  ->
         let uu____52664 = lowercase_module_name f  in
         add_entry uu____52664 f) filenames;
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
        (let uu____52696 =
           let uu____52700 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____52700  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____52736 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____52736  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____52696);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____52900 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____52900 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____52923 = string_of_lid l last1  in
      FStar_String.lowercase uu____52923
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____52932 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____52932
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____52954 =
        let uu____52956 =
          let uu____52958 =
            let uu____52960 =
              let uu____52964 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____52964  in
            FStar_Util.must uu____52960  in
          FStar_String.lowercase uu____52958  in
        uu____52956 <> k'  in
      if uu____52954
      then
        let uu____52969 = FStar_Ident.range_of_lid lid  in
        let uu____52970 =
          let uu____52976 =
            let uu____52978 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____52978 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____52976)  in
        FStar_Errors.log_issue uu____52969 uu____52970
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____52994 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____53016 = FStar_Options.prims_basename ()  in
      let uu____53018 =
        let uu____53022 = FStar_Options.pervasives_basename ()  in
        let uu____53024 =
          let uu____53028 = FStar_Options.pervasives_native_basename ()  in
          [uu____53028]  in
        uu____53022 :: uu____53024  in
      uu____53016 :: uu____53018  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____53071 =
         let uu____53074 = lowercase_module_name full_filename  in
         namespace_of_module uu____53074  in
       match uu____53071 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____53113 -> d = d'
  
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
        let uu____53153 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____53153
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____53188 =
             let uu____53189 = is_interface filename  in
             if uu____53189
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____53396 =
               let uu____53398 =
                 let uu____53400 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____53400  in
               Prims.op_Negation uu____53398  in
             if uu____53396
             then
               let uu____53469 =
                 let uu____53472 = FStar_ST.op_Bang deps1  in d ::
                   uu____53472
                  in
               FStar_ST.op_Colon_Equals deps1 uu____53469
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____53653 =
               resolve_module_name original_or_working_map key  in
             match uu____53653 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____53696 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____53696
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____53735 -> false  in
           let record_open_module let_open lid =
             let uu____53754 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____53754
             then true
             else
               (if let_open
                then
                  (let uu____53763 = FStar_Ident.range_of_lid lid  in
                   let uu____53764 =
                     let uu____53770 =
                       let uu____53772 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____53772
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____53770)
                      in
                   FStar_Errors.log_issue uu____53763 uu____53764)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____53792 = FStar_Ident.range_of_lid lid  in
               let uu____53793 =
                 let uu____53799 =
                   let uu____53801 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____53801
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____53799)
                  in
               FStar_Errors.log_issue uu____53792 uu____53793
             else ()  in
           let record_open let_open lid =
             let uu____53821 = record_open_module let_open lid  in
             if uu____53821
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____53838 =
             match uu____53838 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____53845 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____53862 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____53862  in
             let alias = lowercase_join_longident lid true  in
             let uu____53867 = FStar_Util.smap_try_find original_map alias
                in
             match uu____53867 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____53935 = FStar_Ident.range_of_lid lid  in
                   let uu____53936 =
                     let uu____53942 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____53942)
                      in
                   FStar_Errors.log_issue uu____53935 uu____53936);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____53953 = add_dependence_edge working_map module_name
                in
             if uu____53953
             then ()
             else
               (let uu____53958 = FStar_Options.debug_any ()  in
                if uu____53958
                then
                  let uu____53961 = FStar_Ident.range_of_lid module_name  in
                  let uu____53962 =
                    let uu____53968 =
                      let uu____53970 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____53970
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____53968)
                     in
                  FStar_Errors.log_issue uu____53961 uu____53962
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____53982 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_54110 =
              match uu___426_54110 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____54121 =
                        let uu____54123 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____54123
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____54129) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____54140 =
                        let uu____54142 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____54142
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
                  let uu____54164 =
                    let uu____54165 = lowercase_join_longident lid true  in
                    FriendImplementation uu____54165  in
                  add_dep deps uu____54164
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____54203 = record_module_alias ident lid  in
                  if uu____54203
                  then
                    let uu____54206 =
                      let uu____54207 = lowercase_join_longident lid true  in
                      dep_edge uu____54207  in
                    add_dep deps uu____54206
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____54245,patterms) ->
                  FStar_List.iter
                    (fun uu____54267  ->
                       match uu____54267 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____54276,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____54282,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54284;
                    FStar_Parser_AST.mdest = uu____54285;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54287;
                    FStar_Parser_AST.mdest = uu____54288;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____54290,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54292;
                    FStar_Parser_AST.mdest = uu____54293;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____54297,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____54336  ->
                           match uu____54336 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____54349,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____54356 -> ()
              | FStar_Parser_AST.Pragma uu____54357 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____54393 =
                      let uu____54395 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____54395 > (Prims.parse_int "1")  in
                    if uu____54393
                    then
                      let uu____54442 =
                        let uu____54448 =
                          let uu____54450 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____54450
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____54448)
                         in
                      let uu____54455 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____54442 uu____54455
                    else ()))
            
            and collect_tycon uu___427_54458 =
              match uu___427_54458 with
              | FStar_Parser_AST.TyconAbstract (uu____54459,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____54471,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____54485,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____54531  ->
                        match uu____54531 with
                        | (uu____54540,t,uu____54542) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____54547,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____54609  ->
                        match uu____54609 with
                        | (uu____54623,t,uu____54625,uu____54626) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_54637 =
              match uu___428_54637 with
              | FStar_Parser_AST.DefineEffect (uu____54638,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____54652,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____54665,t);
                   FStar_Parser_AST.brange = uu____54667;
                   FStar_Parser_AST.blevel = uu____54668;
                   FStar_Parser_AST.aqual = uu____54669;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____54672,t);
                   FStar_Parser_AST.brange = uu____54674;
                   FStar_Parser_AST.blevel = uu____54675;
                   FStar_Parser_AST.aqual = uu____54676;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____54680;
                   FStar_Parser_AST.blevel = uu____54681;
                   FStar_Parser_AST.aqual = uu____54682;_} -> collect_term t
               | uu____54685 -> ())
            
            and collect_aqual uu___429_54686 =
              match uu___429_54686 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____54690 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_54694 =
              match uu___430_54694 with
              | FStar_Const.Const_int
                  (uu____54695,FStar_Pervasives_Native.Some
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
                  let uu____54722 =
                    let uu____54723 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____54723  in
                  add_dep deps uu____54722
              | FStar_Const.Const_char uu____54759 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____54795 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____54830 -> ()
            
            and collect_term' uu___433_54831 =
              match uu___433_54831 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____54840 =
                      let uu____54842 = FStar_Ident.text_of_id s  in
                      uu____54842 = "@"  in
                    if uu____54840
                    then
                      let uu____54847 =
                        let uu____54848 =
                          let uu____54849 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____54849
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____54848  in
                      collect_term' uu____54847
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____54853 -> ()
              | FStar_Parser_AST.Uvar uu____54854 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____54857) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (if (FStar_List.length termimps) = (Prims.parse_int "1")
                   then record_lid lid
                   else ();
                   FStar_List.iter
                     (fun uu____54891  ->
                        match uu____54891 with
                        | (t,uu____54897) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____54907) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____54909,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____54959  ->
                        match uu____54959 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____54988 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____54998,t1,t2) ->
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
                     (fun uu____55094  ->
                        match uu____55094 with
                        | (uu____55099,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____55102) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_55131  ->
                        match uu___431_55131 with
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
              | FStar_Parser_AST.NamedTyp (uu____55179,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____55183) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____55191) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____55199,uu____55200) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____55206) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____55220 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____55220);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_55230  ->
                        match uu___432_55230 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_55240 =
              match uu___434_55240 with
              | FStar_Parser_AST.PatVar (uu____55241,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____55247,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____55256 -> ()
              | FStar_Parser_AST.PatConst uu____55257 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____55265 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____55273) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____55294  ->
                       match uu____55294 with
                       | (uu____55299,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____55344 =
              match uu____55344 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____55362 = FStar_Parser_Driver.parse_file filename  in
            match uu____55362 with
            | (ast,uu____55375) ->
                let mname = lowercase_module_name filename  in
                ((let uu____55393 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____55393
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____55432 = FStar_ST.op_Bang deps  in
                  let uu____55480 = FStar_ST.op_Bang mo_roots  in
                  let uu____55528 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____55432;
                    additional_roots = uu____55480;
                    has_inline_for_extraction = uu____55528
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____55600 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____55600 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____55722 = dep_graph  in
    match uu____55722 with
    | Deps g -> let uu____55726 = FStar_Util.smap_copy g  in Deps uu____55726
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____55871 filename =
              match uu____55871 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____55912 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____55912  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____55943 = FStar_Options.debug_any ()  in
                         if uu____55943
                         then
                           let uu____55946 =
                             let uu____55948 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____55948  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____55946
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1246_55959 = dep_node  in
                           { edges = (uu___1246_55959.edges); color = Gray });
                        (let uu____55960 =
                           let uu____55971 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____55971
                            in
                         match uu____55960 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1252_56007 = dep_node  in
                                 {
                                   edges = (uu___1252_56007.edges);
                                   color = Black
                                 });
                              (let uu____56009 = FStar_Options.debug_any ()
                                  in
                               if uu____56009
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____56015 =
                                 let uu____56019 =
                                   FStar_List.collect
                                     (fun uu___435_56026  ->
                                        match uu___435_56026 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____56019 all_friends1
                                  in
                               (uu____56015, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____56092 = FStar_Options.debug_any ()  in
             if uu____56092
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____56121 = deps  in
               match uu____56121 with
               | Deps dg ->
                   let uu____56125 = deps_empty ()  in
                   (match uu____56125 with
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
                                  | uu____56197 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____56205  ->
                                  let uu____56207 =
                                    let uu___1287_56208 = dep_node  in
                                    let uu____56209 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____56209; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____56207) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____56211 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____56211
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____56216 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____56216 with
             | (friends,all_files_0) ->
                 ((let uu____56259 = FStar_Options.debug_any ()  in
                   if uu____56259
                   then
                     let uu____56262 =
                       let uu____56264 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____56264  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____56262
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____56283 =
                     (let uu____56295 = FStar_Options.debug_any ()  in
                      if uu____56295
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____56283 with
                   | (uu____56318,all_files) ->
                       ((let uu____56333 = FStar_Options.debug_any ()  in
                         if uu____56333
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____56340 = FStar_ST.op_Bang widened  in
                         (all_files, uu____56340))))))
  
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
                let uu____56448 = FStar_Options.find_file fn  in
                match uu____56448 with
                | FStar_Pervasives_Native.None  ->
                    let uu____56454 =
                      let uu____56460 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____56460)
                       in
                    FStar_Errors.raise_err uu____56454
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____56490 =
          let uu____56494 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____56494  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____56490  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____56605 =
          let uu____56607 = deps_try_find dep_graph file_name  in
          uu____56607 = FStar_Pervasives_Native.None  in
        if uu____56605
        then
          let uu____56613 =
            let uu____56625 =
              let uu____56639 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____56639 file_name  in
            match uu____56625 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____56613 with
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
                  let uu____56783 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____56783
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____56791 = FStar_List.unique deps1  in
                  { edges = uu____56791; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____56793 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____56793)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____56833 =
            let uu____56839 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____56839)  in
          FStar_Errors.raise_err uu____56833)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____56876 = deps_try_find dep_graph1 filename  in
             match uu____56876 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____56880 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____56880
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____56894 =
                           implementation_of file_system_map f  in
                         (match uu____56894 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____56905 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____56911 =
                           implementation_of file_system_map f  in
                         (match uu____56911 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____56922 -> [x; UseImplementation f])
                     | uu____56926 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1371_56929 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____56931 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____56931);
                deps_add_dep dep_graph1 filename
                  (let uu___1376_56941 = node  in
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
        let uu____57007 =
          let uu____57016 =
            let uu____57018 = FStar_Options.codegen ()  in
            uu____57018 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____57016
           in
        match uu____57007 with
        | (all_files,uu____57031) ->
            ((let uu____57041 = FStar_Options.debug_any ()  in
              if uu____57041
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
        (Prims.string * Prims.string) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun deps  ->
    fun fn  ->
      fun cache_file  ->
        let file_system_map = deps.file_system_map  in
        let all_cmd_line_files = deps.cmd_line_files  in
        let deps1 = deps.dep_graph  in
        let fn1 =
          let uu____57108 = FStar_Options.find_file fn  in
          match uu____57108 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____57116 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____57130 = FStar_Options.debug_any ()  in
           if uu____57130
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____57149 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____57149
          then
            let uu____57160 =
              let uu____57167 =
                let uu____57169 =
                  let uu____57171 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____57171  in
                digest_of_file1 uu____57169  in
              ("interface", uu____57167)  in
            [uu____57160]
          else []  in
        let binary_deps =
          let uu____57203 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____57203
            (FStar_List.filter
               (fun fn2  ->
                  let uu____57218 =
                    (is_interface fn2) &&
                      (let uu____57221 = lowercase_module_name fn2  in
                       uu____57221 = module_name)
                     in
                  Prims.op_Negation uu____57218))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____57237 = lowercase_module_name fn11  in
                 let uu____57239 = lowercase_module_name fn2  in
                 FStar_String.compare uu____57237 uu____57239) binary_deps
           in
        let rec hash_deps out uu___436_57272 =
          match uu___436_57272 with
          | [] ->
              FStar_Pervasives_Native.Some
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____57335 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____57335
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____57353 = FStar_Options.debug_any ()  in
                     if uu____57353
                     then
                       let uu____57356 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____57356
                     else ());
                    FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some dig ->
                   let uu____57372 =
                     let uu____57381 =
                       let uu____57388 = lowercase_module_name fn2  in
                       (uu____57388, dig)  in
                     uu____57381 :: out  in
                   hash_deps uu____57372 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____57428 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____57454  ->
              match uu____57454 with
              | (m,d) ->
                  let uu____57468 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____57468))
       in
    FStar_All.pipe_right uu____57428 (FStar_String.concat "\n")
  
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
              let uu____57503 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____57503 FStar_Option.get  in
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
    let uu____57532 = deps.dep_graph  in
    match uu____57532 with
    | Deps deps1 ->
        let uu____57536 =
          let uu____57538 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____57556 =
                       let uu____57558 =
                         let uu____57560 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____57560
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____57558
                        in
                     uu____57556 :: out) []
             in
          FStar_All.pipe_right uu____57538 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____57536 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____57632 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____57632) ||
          (let uu____57639 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____57639)
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
            let uu____57682 =
              let uu____57686 = FStar_ST.op_Bang order  in ml_file ::
                uu____57686
               in
            FStar_ST.op_Colon_Equals order uu____57682
         in
      let rec aux uu___437_57793 =
        match uu___437_57793 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____57821 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____57821 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____57824 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____57824
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____57828;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____57837 = should_visit lc_module_name  in
              if uu____57837
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____57845 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____57845);
                 (let uu____57850 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____57850);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____57862 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____57862)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____57936 =
          let uu____57938 =
            let uu____57942 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____57942  in
          FStar_Option.get uu____57938  in
        FStar_Util.replace_chars uu____57936 46 "_"  in
      let uu____57947 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____57947  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____57969 = output_file ".ml" f  in norm_path uu____57969  in
    let output_krml_file f =
      let uu____57981 = output_file ".krml" f  in norm_path uu____57981  in
    let output_cmx_file f =
      let uu____57993 = output_file ".cmx" f  in norm_path uu____57993  in
    let cache_file f =
      let uu____58010 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____58010
        (fun uu____58039  ->
           match uu____58039 with | (f1,b) -> ((norm_path f1), b))
       in
    let set_of_unchecked_files =
      let uu____58064 =
        let uu____58075 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____58112 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____58112 FStar_Option.get  in
               let iface_deps =
                 let uu____58122 = is_interface file_name  in
                 if uu____58122
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____58133 =
                      let uu____58137 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____58137  in
                    match uu____58133 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____58149 =
                          let uu____58152 =
                            let uu____58153 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____58153  in
                          uu____58152.edges  in
                        FStar_Pervasives_Native.Some uu____58149)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____58170 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____58170))
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
               let files4 = FStar_String.concat "\\\n\t" files3  in
               let uu____58229 = cache_file file_name  in
               match uu____58229 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let uu____58258 =
                       let uu____58267 = FStar_Options.cmi ()  in
                       if uu____58267
                       then
                         topological_dependences_of deps.file_system_map
                           deps.dep_graph deps.interfaces_with_inlining
                           [file_name] true
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
                          let uu____58315 =
                            FStar_Util.remove_dups
                              (fun x  -> fun y  -> x = y)
                              (FStar_List.append fst_files
                                 fst_files_from_iface)
                             in
                          (uu____58315, false))
                        in
                     match uu____58258 with
                     | (all_fst_files_dep,widened) ->
                         let all_checked_fst_dep_files =
                           FStar_All.pipe_right all_fst_files_dep
                             (FStar_List.map
                                (fun f  ->
                                   let uu____58362 =
                                     FStar_All.pipe_right f cache_file  in
                                   FStar_All.pipe_right uu____58362
                                     FStar_Pervasives_Native.fst))
                            in
                         ((let uu____58386 = is_implementation file_name  in
                           if uu____58386
                           then
                             ((let uu____58390 =
                                 (FStar_Options.cmi ()) && widened  in
                               if uu____58390
                               then
                                 ((let uu____58394 = output_ml_file file_name
                                      in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____58394 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files));
                                  (let uu____58398 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____58398 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)))
                               else
                                 ((let uu____58405 = output_ml_file file_name
                                      in
                                   FStar_Util.print2 "%s: %s \n\n"
                                     uu____58405 cache_file_name1);
                                  (let uu____58408 =
                                     output_krml_file file_name  in
                                   FStar_Util.print2 "%s: %s\n\n" uu____58408
                                     cache_file_name1)));
                              (let cmx_files =
                                 let extracted_fst_files =
                                   FStar_All.pipe_right all_fst_files_dep
                                     (FStar_List.filter
                                        (fun df  ->
                                           (let uu____58433 =
                                              lowercase_module_name df  in
                                            let uu____58435 =
                                              lowercase_module_name file_name
                                               in
                                            uu____58433 <> uu____58435) &&
                                             (let uu____58439 =
                                                lowercase_module_name df  in
                                              FStar_Options.should_extract
                                                uu____58439)))
                                    in
                                 FStar_All.pipe_right extracted_fst_files
                                   (FStar_List.map output_cmx_file)
                                  in
                               let uu____58449 =
                                 let uu____58451 =
                                   lowercase_module_name file_name  in
                                 FStar_Options.should_extract uu____58451  in
                               if uu____58449
                               then
                                 let uu____58454 = output_cmx_file file_name
                                    in
                                 let uu____58456 = output_ml_file file_name
                                    in
                                 FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                   uu____58454 uu____58456
                                   (FStar_String.concat "\\\n\t" cmx_files)
                               else ()))
                           else
                             (let uu____58464 =
                                (let uu____58468 =
                                   let uu____58470 =
                                     lowercase_module_name file_name  in
                                   has_implementation deps.file_system_map
                                     uu____58470
                                    in
                                 Prims.op_Negation uu____58468) &&
                                  (is_interface file_name)
                                 in
                              if uu____58464
                              then
                                let uu____58473 =
                                  (FStar_Options.cmi ()) && widened  in
                                (if uu____58473
                                 then
                                   let uu____58476 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____58476 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)
                                 else
                                   (let uu____58482 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____58482 cache_file_name1))
                              else ()));
                          set_of_unchecked_files1)))) uu____58075
         in
      FStar_All.pipe_right keys uu____58064  in
    let uu____58493 =
      let uu____58504 =
        let uu____58508 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____58508
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____58504
        (fun l  ->
           let uu____58545 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____58545))
       in
    match uu____58493 with
    | (all_fst_files,all_unchecked_fst_files) ->
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____58603 = FStar_Options.should_extract mname  in
                  if uu____58603
                  then
                    let uu____58606 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____58606
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____58633 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____58633));
          sort_output_files krml_file_map  in
        ((let uu____58637 =
            let uu____58639 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58639 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____58637);
         (let uu____58658 =
            let uu____58660 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58660 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n"
            uu____58658);
         (let uu____58679 =
            let uu____58681 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58681 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____58679);
         (let uu____58699 =
            let uu____58701 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58701 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____58699))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____58725 = FStar_Options.dep ()  in
    match uu____58725 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____58737 ->
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
         fun uu____58792  ->
           fun s  ->
             match uu____58792 with
             | (v0,v1) ->
                 let uu____58821 =
                   let uu____58823 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____58823  in
                 FStar_String.op_Hat s uu____58821) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____58844 =
        let uu____58846 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____58846  in
      has_interface deps.file_system_map uu____58844
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____58862 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____58862  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____58873 =
                   let uu____58875 = module_name_of_file f  in
                   FStar_String.lowercase uu____58875  in
                 uu____58873 = m)))
  