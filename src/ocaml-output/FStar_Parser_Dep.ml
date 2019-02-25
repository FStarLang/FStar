open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____50424 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____50435 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____50446 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____50469 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____50480 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____50491 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____50502 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____50513 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____50561 =
             (l > lext) &&
               (let uu____50574 = FStar_String.substring f (l - lext) lext
                   in
                uu____50574 = ext)
              in
           if uu____50561
           then
             let uu____50595 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____50595
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____50612 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____50612 with
    | (FStar_Pervasives_Native.Some m)::uu____50626 ->
        FStar_Pervasives_Native.Some m
    | uu____50638 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____50655 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____50655 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____50669 = is_interface f  in Prims.op_Negation uu____50669
  
let list_of_option :
  'Auu____50676 .
    'Auu____50676 FStar_Pervasives_Native.option -> 'Auu____50676 Prims.list
  =
  fun uu___423_50685  ->
    match uu___423_50685 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____50694 .
    ('Auu____50694 FStar_Pervasives_Native.option * 'Auu____50694
      FStar_Pervasives_Native.option) -> 'Auu____50694 Prims.list
  =
  fun uu____50709  ->
    match uu____50709 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____50737 =
      let uu____50741 = FStar_Util.basename f  in
      check_and_strip_suffix uu____50741  in
    match uu____50737 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____50748 =
          let uu____50754 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____50754)  in
        FStar_Errors.raise_err uu____50748
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____50768 = module_name_of_file f  in
    FStar_String.lowercase uu____50768
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____50781 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____50781 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____50784 ->
        let uu____50787 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____50787
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____50829 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____50853 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____50877 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____50901 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_50920  ->
    match uu___424_50920 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____50939 . unit -> 'Auu____50939 Prims.list =
  fun uu____50942  -> [] 
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
  fun uu____51284  ->
    fun k  -> match uu____51284 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____51306  ->
    fun k  ->
      fun v1  ->
        match uu____51306 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____51321  ->
    match uu____51321 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____51333  ->
    let uu____51334 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____51334
  
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
  let uu____51392 = deps_empty ()  in
  let uu____51393 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____51405 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____51392 uu____51393 [] [] [] uu____51405 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_51418  ->
    match uu___425_51418 with
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
      let uu____51447 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51447 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____51474) ->
          let uu____51496 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____51496
      | FStar_Pervasives_Native.Some
          (uu____51499,FStar_Pervasives_Native.Some fn) ->
          let uu____51522 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____51522
      | uu____51525 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51558 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51558 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____51585) ->
          FStar_Pervasives_Native.Some iface
      | uu____51608 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51641 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51641 with
      | FStar_Pervasives_Native.Some
          (uu____51667,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____51691 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____51720 = interface_of file_system_map key  in
      FStar_Option.isSome uu____51720
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51740 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____51740
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____51767 =
        let uu____51769 = FStar_Options.lax ()  in
        if uu____51769 then ".checked.lax" else ".checked"  in
      FStar_String.op_Hat fn uu____51767  in
    let uu____51777 =
      let uu____51781 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____51781  in
    match uu____51777 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____51802 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____51802
        then
          let uu____51813 =
            let uu____51819 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____51819)
             in
          FStar_Errors.raise_err uu____51813
        else
          (let uu____51831 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____51831, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____51845 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____51845 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____51881 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____51881 FStar_Util.must
  
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
                      (let uu____51935 = lowercase_module_name fn  in
                       key = uu____51935)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____51954 = interface_of file_system_map key  in
              (match uu____51954 with
               | FStar_Pervasives_Native.None  ->
                   let uu____51961 =
                     let uu____51967 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____51967)  in
                   FStar_Errors.raise_err uu____51961
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____51977 =
                (cmd_line_has_impl key) &&
                  (let uu____51980 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____51980)
                 in
              if uu____51977
              then
                let uu____51987 = FStar_Options.expose_interfaces ()  in
                (if uu____51987
                 then
                   let uu____51991 =
                     let uu____51993 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____51993  in
                   maybe_use_cache_of uu____51991
                 else
                   (let uu____52000 =
                      let uu____52006 =
                        let uu____52008 =
                          let uu____52010 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____52010  in
                        let uu____52015 =
                          let uu____52017 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____52017  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____52008 uu____52015
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____52006)
                       in
                    FStar_Errors.raise_err uu____52000))
              else
                (let uu____52027 =
                   let uu____52029 = interface_of file_system_map key  in
                   FStar_Option.get uu____52029  in
                 maybe_use_cache_of uu____52027)
          | PreferInterface key ->
              let uu____52036 = implementation_of file_system_map key  in
              (match uu____52036 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52042 =
                     let uu____52048 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52048)
                      in
                   FStar_Errors.raise_err uu____52042
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____52058 = implementation_of file_system_map key  in
              (match uu____52058 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52064 =
                     let uu____52070 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52070)
                      in
                   FStar_Errors.raise_err uu____52064
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____52080 = implementation_of file_system_map key  in
              (match uu____52080 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52086 =
                     let uu____52092 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52092)
                      in
                   FStar_Errors.raise_err uu____52086
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
          let uu____52153 = deps_try_find deps fn  in
          match uu____52153 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____52161;_} ->
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
    (let uu____52175 =
       let uu____52177 =
         let uu____52179 =
           let uu____52181 =
             let uu____52185 =
               let uu____52189 = deps_keys graph  in
               FStar_List.unique uu____52189  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____52203 =
                      let uu____52204 = deps_try_find graph k  in
                      FStar_Util.must uu____52204  in
                    uu____52203.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____52225 =
                      let uu____52227 = lowercase_module_name k  in
                      r uu____52227  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____52225
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____52185
              in
           FStar_String.concat "\n" uu____52181  in
         FStar_String.op_Hat uu____52179 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____52177  in
     FStar_Util.write_file "dep.graph" uu____52175)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____52248  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____52274 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____52274  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____52314 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____52314
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____52351 =
              let uu____52357 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____52357)  in
            FStar_Errors.raise_err uu____52351)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____52420 = FStar_Util.smap_try_find map1 key  in
      match uu____52420 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____52467 = is_interface full_path  in
          if uu____52467
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____52516 = is_interface full_path  in
          if uu____52516
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____52558 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____52576  ->
          match uu____52576 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____52558);
    FStar_List.iter
      (fun f  ->
         let uu____52595 = lowercase_module_name f  in
         add_entry uu____52595 f) filenames;
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
        (let uu____52627 =
           let uu____52631 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____52631  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____52667 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____52667  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____52627);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____52831 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____52831 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____52854 = string_of_lid l last1  in
      FStar_String.lowercase uu____52854
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____52863 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____52863
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____52885 =
        let uu____52887 =
          let uu____52889 =
            let uu____52891 =
              let uu____52895 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____52895  in
            FStar_Util.must uu____52891  in
          FStar_String.lowercase uu____52889  in
        uu____52887 <> k'  in
      if uu____52885
      then
        let uu____52900 = FStar_Ident.range_of_lid lid  in
        let uu____52901 =
          let uu____52907 =
            let uu____52909 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____52909 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____52907)  in
        FStar_Errors.log_issue uu____52900 uu____52901
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____52925 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____52947 = FStar_Options.prims_basename ()  in
      let uu____52949 =
        let uu____52953 = FStar_Options.pervasives_basename ()  in
        let uu____52955 =
          let uu____52959 = FStar_Options.pervasives_native_basename ()  in
          [uu____52959]  in
        uu____52953 :: uu____52955  in
      uu____52947 :: uu____52949  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____53002 =
         let uu____53005 = lowercase_module_name full_filename  in
         namespace_of_module uu____53005  in
       match uu____53002 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____53044 -> d = d'
  
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
        let uu____53084 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____53084
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____53119 =
             let uu____53120 = is_interface filename  in
             if uu____53120
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____53327 =
               let uu____53329 =
                 let uu____53331 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____53331  in
               Prims.op_Negation uu____53329  in
             if uu____53327
             then
               let uu____53400 =
                 let uu____53403 = FStar_ST.op_Bang deps1  in d ::
                   uu____53403
                  in
               FStar_ST.op_Colon_Equals deps1 uu____53400
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____53584 =
               resolve_module_name original_or_working_map key  in
             match uu____53584 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____53627 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____53627
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____53666 -> false  in
           let record_open_module let_open lid =
             let uu____53685 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____53685
             then true
             else
               (if let_open
                then
                  (let uu____53694 = FStar_Ident.range_of_lid lid  in
                   let uu____53695 =
                     let uu____53701 =
                       let uu____53703 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____53703
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____53701)
                      in
                   FStar_Errors.log_issue uu____53694 uu____53695)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____53723 = FStar_Ident.range_of_lid lid  in
               let uu____53724 =
                 let uu____53730 =
                   let uu____53732 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____53732
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____53730)
                  in
               FStar_Errors.log_issue uu____53723 uu____53724
             else ()  in
           let record_open let_open lid =
             let uu____53752 = record_open_module let_open lid  in
             if uu____53752
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____53769 =
             match uu____53769 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____53776 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____53793 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____53793  in
             let alias = lowercase_join_longident lid true  in
             let uu____53798 = FStar_Util.smap_try_find original_map alias
                in
             match uu____53798 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____53866 = FStar_Ident.range_of_lid lid  in
                   let uu____53867 =
                     let uu____53873 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____53873)
                      in
                   FStar_Errors.log_issue uu____53866 uu____53867);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____53884 = add_dependence_edge working_map module_name
                in
             if uu____53884
             then ()
             else
               (let uu____53889 = FStar_Options.debug_any ()  in
                if uu____53889
                then
                  let uu____53892 = FStar_Ident.range_of_lid module_name  in
                  let uu____53893 =
                    let uu____53899 =
                      let uu____53901 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____53901
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____53899)
                     in
                  FStar_Errors.log_issue uu____53892 uu____53893
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____53913 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_54041 =
              match uu___426_54041 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____54052 =
                        let uu____54054 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____54054
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____54060) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____54071 =
                        let uu____54073 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____54073
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
                  let uu____54095 =
                    let uu____54096 = lowercase_join_longident lid true  in
                    FriendImplementation uu____54096  in
                  add_dep deps uu____54095
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____54134 = record_module_alias ident lid  in
                  if uu____54134
                  then
                    let uu____54137 =
                      let uu____54138 = lowercase_join_longident lid true  in
                      dep_edge uu____54138  in
                    add_dep deps uu____54137
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____54176,patterms) ->
                  FStar_List.iter
                    (fun uu____54198  ->
                       match uu____54198 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____54207,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____54213,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54215;
                    FStar_Parser_AST.mdest = uu____54216;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54218;
                    FStar_Parser_AST.mdest = uu____54219;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____54221,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54223;
                    FStar_Parser_AST.mdest = uu____54224;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____54228,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____54267  ->
                           match uu____54267 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____54280,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____54287 -> ()
              | FStar_Parser_AST.Pragma uu____54288 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____54324 =
                      let uu____54326 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____54326 > (Prims.parse_int "1")  in
                    if uu____54324
                    then
                      let uu____54373 =
                        let uu____54379 =
                          let uu____54381 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____54381
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____54379)
                         in
                      let uu____54386 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____54373 uu____54386
                    else ()))
            
            and collect_tycon uu___427_54389 =
              match uu___427_54389 with
              | FStar_Parser_AST.TyconAbstract (uu____54390,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____54402,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____54416,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____54462  ->
                        match uu____54462 with
                        | (uu____54471,t,uu____54473) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____54478,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____54540  ->
                        match uu____54540 with
                        | (uu____54554,t,uu____54556,uu____54557) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_54568 =
              match uu___428_54568 with
              | FStar_Parser_AST.DefineEffect (uu____54569,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____54583,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____54596,t);
                   FStar_Parser_AST.brange = uu____54598;
                   FStar_Parser_AST.blevel = uu____54599;
                   FStar_Parser_AST.aqual = uu____54600;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____54603,t);
                   FStar_Parser_AST.brange = uu____54605;
                   FStar_Parser_AST.blevel = uu____54606;
                   FStar_Parser_AST.aqual = uu____54607;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____54611;
                   FStar_Parser_AST.blevel = uu____54612;
                   FStar_Parser_AST.aqual = uu____54613;_} -> collect_term t
               | uu____54616 -> ())
            
            and collect_aqual uu___429_54617 =
              match uu___429_54617 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____54621 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_54625 =
              match uu___430_54625 with
              | FStar_Const.Const_int
                  (uu____54626,FStar_Pervasives_Native.Some
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
                  let uu____54653 =
                    let uu____54654 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____54654  in
                  add_dep deps uu____54653
              | FStar_Const.Const_char uu____54690 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____54726 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____54761 -> ()
            
            and collect_term' uu___433_54762 =
              match uu___433_54762 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____54771 =
                      let uu____54773 = FStar_Ident.text_of_id s  in
                      uu____54773 = "@"  in
                    if uu____54771
                    then
                      let uu____54778 =
                        let uu____54779 =
                          let uu____54780 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____54780
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____54779  in
                      collect_term' uu____54778
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____54784 -> ()
              | FStar_Parser_AST.Uvar uu____54785 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____54788) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (if (FStar_List.length termimps) = (Prims.parse_int "1")
                   then record_lid lid
                   else ();
                   FStar_List.iter
                     (fun uu____54822  ->
                        match uu____54822 with
                        | (t,uu____54828) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____54838) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____54840,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____54890  ->
                        match uu____54890 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____54919 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____54929,t1,t2) ->
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
                     (fun uu____55025  ->
                        match uu____55025 with
                        | (uu____55030,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____55033) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_55062  ->
                        match uu___431_55062 with
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
              | FStar_Parser_AST.NamedTyp (uu____55110,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____55114) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____55122) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____55130,uu____55131) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____55137) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____55151 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____55151);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_55161  ->
                        match uu___432_55161 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_55171 =
              match uu___434_55171 with
              | FStar_Parser_AST.PatVar (uu____55172,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____55178,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____55187 -> ()
              | FStar_Parser_AST.PatConst uu____55188 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____55196 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____55204) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____55225  ->
                       match uu____55225 with
                       | (uu____55230,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____55275 =
              match uu____55275 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____55293 = FStar_Parser_Driver.parse_file filename  in
            match uu____55293 with
            | (ast,uu____55306) ->
                let mname = lowercase_module_name filename  in
                ((let uu____55324 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____55324
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____55363 = FStar_ST.op_Bang deps  in
                  let uu____55411 = FStar_ST.op_Bang mo_roots  in
                  let uu____55459 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____55363;
                    additional_roots = uu____55411;
                    has_inline_for_extraction = uu____55459
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____55531 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____55531 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____55653 = dep_graph  in
    match uu____55653 with
    | Deps g -> let uu____55657 = FStar_Util.smap_copy g  in Deps uu____55657
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____55802 filename =
              match uu____55802 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____55843 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____55843  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____55874 = FStar_Options.debug_any ()  in
                         if uu____55874
                         then
                           let uu____55877 =
                             let uu____55879 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____55879  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____55877
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1246_55890 = dep_node  in
                           { edges = (uu___1246_55890.edges); color = Gray });
                        (let uu____55891 =
                           let uu____55902 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____55902
                            in
                         match uu____55891 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1252_55938 = dep_node  in
                                 {
                                   edges = (uu___1252_55938.edges);
                                   color = Black
                                 });
                              (let uu____55940 = FStar_Options.debug_any ()
                                  in
                               if uu____55940
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____55946 =
                                 let uu____55950 =
                                   FStar_List.collect
                                     (fun uu___435_55957  ->
                                        match uu___435_55957 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____55950 all_friends1
                                  in
                               (uu____55946, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____56023 = FStar_Options.debug_any ()  in
             if uu____56023
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____56052 = deps  in
               match uu____56052 with
               | Deps dg ->
                   let uu____56056 = deps_empty ()  in
                   (match uu____56056 with
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
                                  | uu____56128 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____56136  ->
                                  let uu____56138 =
                                    let uu___1287_56139 = dep_node  in
                                    let uu____56140 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____56140; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____56138) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____56142 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____56142
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____56147 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____56147 with
             | (friends,all_files_0) ->
                 ((let uu____56190 = FStar_Options.debug_any ()  in
                   if uu____56190
                   then
                     let uu____56193 =
                       let uu____56195 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____56195  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____56193
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____56214 =
                     (let uu____56226 = FStar_Options.debug_any ()  in
                      if uu____56226
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____56214 with
                   | (uu____56249,all_files) ->
                       ((let uu____56264 = FStar_Options.debug_any ()  in
                         if uu____56264
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____56271 = FStar_ST.op_Bang widened  in
                         (all_files, uu____56271))))))
  
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
                let uu____56379 = FStar_Options.find_file fn  in
                match uu____56379 with
                | FStar_Pervasives_Native.None  ->
                    let uu____56385 =
                      let uu____56391 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____56391)
                       in
                    FStar_Errors.raise_err uu____56385
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____56421 =
          let uu____56425 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____56425  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____56421  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____56536 =
          let uu____56538 = deps_try_find dep_graph file_name  in
          uu____56538 = FStar_Pervasives_Native.None  in
        if uu____56536
        then
          let uu____56544 =
            let uu____56556 =
              let uu____56570 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____56570 file_name  in
            match uu____56556 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____56544 with
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
                  let uu____56714 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____56714
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____56722 = FStar_List.unique deps1  in
                  { edges = uu____56722; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____56724 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____56724)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____56764 =
            let uu____56770 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____56770)  in
          FStar_Errors.raise_err uu____56764)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____56807 = deps_try_find dep_graph1 filename  in
             match uu____56807 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____56811 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____56811
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____56825 =
                           implementation_of file_system_map f  in
                         (match uu____56825 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____56836 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____56842 =
                           implementation_of file_system_map f  in
                         (match uu____56842 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____56853 -> [x; UseImplementation f])
                     | uu____56857 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1371_56860 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____56862 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____56862);
                deps_add_dep dep_graph1 filename
                  (let uu___1376_56872 = node  in
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
        let uu____56938 =
          let uu____56947 =
            let uu____56949 = FStar_Options.codegen ()  in
            uu____56949 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____56947
           in
        match uu____56938 with
        | (all_files,uu____56962) ->
            ((let uu____56972 = FStar_Options.debug_any ()  in
              if uu____56972
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
          let uu____57039 = FStar_Options.find_file fn  in
          match uu____57039 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____57047 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____57061 = FStar_Options.debug_any ()  in
           if uu____57061
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____57080 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____57080
          then
            let uu____57091 =
              let uu____57098 =
                let uu____57100 =
                  let uu____57102 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____57102  in
                digest_of_file1 uu____57100  in
              ("interface", uu____57098)  in
            [uu____57091]
          else []  in
        let binary_deps =
          let uu____57134 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____57134
            (FStar_List.filter
               (fun fn2  ->
                  let uu____57149 =
                    (is_interface fn2) &&
                      (let uu____57152 = lowercase_module_name fn2  in
                       uu____57152 = module_name)
                     in
                  Prims.op_Negation uu____57149))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____57168 = lowercase_module_name fn11  in
                 let uu____57170 = lowercase_module_name fn2  in
                 FStar_String.compare uu____57168 uu____57170) binary_deps
           in
        let rec hash_deps out uu___436_57203 =
          match uu___436_57203 with
          | [] ->
              FStar_Pervasives_Native.Some
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____57266 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____57266
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____57284 = FStar_Options.debug_any ()  in
                     if uu____57284
                     then
                       let uu____57287 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____57287
                     else ());
                    FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some dig ->
                   let uu____57303 =
                     let uu____57312 =
                       let uu____57319 = lowercase_module_name fn2  in
                       (uu____57319, dig)  in
                     uu____57312 :: out  in
                   hash_deps uu____57303 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____57359 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____57385  ->
              match uu____57385 with
              | (m,d) ->
                  let uu____57399 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____57399))
       in
    FStar_All.pipe_right uu____57359 (FStar_String.concat "\n")
  
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
              let uu____57434 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____57434 FStar_Option.get  in
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
    let uu____57463 = deps.dep_graph  in
    match uu____57463 with
    | Deps deps1 ->
        let uu____57467 =
          let uu____57469 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____57487 =
                       let uu____57489 =
                         let uu____57491 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____57491
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____57489
                        in
                     uu____57487 :: out) []
             in
          FStar_All.pipe_right uu____57469 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____57467 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____57563 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____57563) ||
          (let uu____57570 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____57570)
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
            let uu____57613 =
              let uu____57617 = FStar_ST.op_Bang order  in ml_file ::
                uu____57617
               in
            FStar_ST.op_Colon_Equals order uu____57613
         in
      let rec aux uu___437_57724 =
        match uu___437_57724 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____57752 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____57752 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____57755 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____57755
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____57759;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____57768 = should_visit lc_module_name  in
              if uu____57768
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____57776 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____57776);
                 (let uu____57781 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____57781);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____57793 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____57793)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____57867 =
          let uu____57869 =
            let uu____57873 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____57873  in
          FStar_Option.get uu____57869  in
        FStar_Util.replace_chars uu____57867 46 "_"  in
      let uu____57878 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____57878  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____57900 = output_file ".ml" f  in norm_path uu____57900  in
    let output_krml_file f =
      let uu____57912 = output_file ".krml" f  in norm_path uu____57912  in
    let output_cmx_file f =
      let uu____57924 = output_file ".cmx" f  in norm_path uu____57924  in
    let cache_file f =
      let uu____57941 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____57941
        (fun uu____57970  ->
           match uu____57970 with | (f1,b) -> ((norm_path f1), b))
       in
    let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")  in
    let set_of_unchecked_files =
      let uu____58021 =
        let uu____58032 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____58071 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____58071 FStar_Option.get  in
               let iface_deps =
                 let uu____58081 = is_interface file_name  in
                 if uu____58081
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____58092 =
                      let uu____58096 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____58096  in
                    match uu____58092 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____58108 =
                          let uu____58111 =
                            let uu____58112 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____58112  in
                          uu____58111.edges  in
                        FStar_Pervasives_Native.Some uu____58108)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____58129 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____58129))
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
               let uu____58188 = cache_file file_name  in
               match uu____58188 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let already_there =
                       let uu____58221 =
                         let uu____58235 =
                           let uu____58237 = output_file ".krml" file_name
                              in
                           norm_path uu____58237  in
                         FStar_Util.smap_try_find transitive_krml uu____58235
                          in
                       match uu____58221 with
                       | FStar_Pervasives_Native.Some
                           (uu____58254,already_there,uu____58256) ->
                           already_there
                       | FStar_Pervasives_Native.None  -> []  in
                     (let uu____58291 =
                        let uu____58293 = output_file ".krml" file_name  in
                        norm_path uu____58293  in
                      let uu____58296 =
                        let uu____58308 =
                          let uu____58310 = output_file ".exe" file_name  in
                          norm_path uu____58310  in
                        let uu____58313 =
                          let uu____58317 =
                            let uu____58321 =
                              let uu____58325 = deps_of deps file_name  in
                              FStar_List.map
                                (fun x  ->
                                   let uu____58335 = output_file ".krml" x
                                      in
                                   norm_path uu____58335) uu____58325
                               in
                            FStar_List.append already_there uu____58321  in
                          FStar_List.unique uu____58317  in
                        (uu____58308, uu____58313, false)  in
                      FStar_Util.smap_add transitive_krml uu____58291
                        uu____58296);
                     (let uu____58357 =
                        let uu____58366 = FStar_Options.cmi ()  in
                        if uu____58366
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
                           let fst_files = maybe_widen_deps dep_node.edges
                              in
                           let fst_files_from_iface =
                             match iface_deps1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some iface_deps2 ->
                                 maybe_widen_deps iface_deps2
                              in
                           let uu____58414 =
                             FStar_Util.remove_dups
                               (fun x  -> fun y  -> x = y)
                               (FStar_List.append fst_files
                                  fst_files_from_iface)
                              in
                           (uu____58414, false))
                         in
                      match uu____58357 with
                      | (all_fst_files_dep,widened) ->
                          let all_checked_fst_dep_files =
                            FStar_All.pipe_right all_fst_files_dep
                              (FStar_List.map
                                 (fun f  ->
                                    let uu____58461 =
                                      FStar_All.pipe_right f cache_file  in
                                    FStar_All.pipe_right uu____58461
                                      FStar_Pervasives_Native.fst))
                             in
                          ((let uu____58485 = is_implementation file_name  in
                            if uu____58485
                            then
                              ((let uu____58489 =
                                  (FStar_Options.cmi ()) && widened  in
                                if uu____58489
                                then
                                  ((let uu____58493 =
                                      output_ml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____58493 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files));
                                   (let uu____58497 =
                                      output_krml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____58497 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files)))
                                else
                                  ((let uu____58504 =
                                      output_ml_file file_name  in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____58504 cache_file_name1);
                                   (let uu____58507 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s\n\n"
                                      uu____58507 cache_file_name1)));
                               (let cmx_files =
                                  let extracted_fst_files =
                                    FStar_All.pipe_right all_fst_files_dep
                                      (FStar_List.filter
                                         (fun df  ->
                                            (let uu____58532 =
                                               lowercase_module_name df  in
                                             let uu____58534 =
                                               lowercase_module_name
                                                 file_name
                                                in
                                             uu____58532 <> uu____58534) &&
                                              (let uu____58538 =
                                                 lowercase_module_name df  in
                                               FStar_Options.should_extract
                                                 uu____58538)))
                                     in
                                  FStar_All.pipe_right extracted_fst_files
                                    (FStar_List.map output_cmx_file)
                                   in
                                let uu____58548 =
                                  let uu____58550 =
                                    lowercase_module_name file_name  in
                                  FStar_Options.should_extract uu____58550
                                   in
                                if uu____58548
                                then
                                  let uu____58553 = output_cmx_file file_name
                                     in
                                  let uu____58555 = output_ml_file file_name
                                     in
                                  FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                    uu____58553 uu____58555
                                    (FStar_String.concat "\\\n\t" cmx_files)
                                else ()))
                            else
                              (let uu____58563 =
                                 (let uu____58567 =
                                    let uu____58569 =
                                      lowercase_module_name file_name  in
                                    has_implementation deps.file_system_map
                                      uu____58569
                                     in
                                  Prims.op_Negation uu____58567) &&
                                   (is_interface file_name)
                                  in
                               if uu____58563
                               then
                                 let uu____58572 =
                                   (FStar_Options.cmi ()) && widened  in
                                 (if uu____58572
                                  then
                                    let uu____58575 =
                                      output_krml_file file_name  in
                                    FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                      uu____58575 cache_file_name1
                                      (FStar_String.concat " \\\n\t"
                                         all_checked_fst_dep_files)
                                  else
                                    (let uu____58581 =
                                       output_krml_file file_name  in
                                     FStar_Util.print2 "%s: %s \n\n"
                                       uu____58581 cache_file_name1))
                               else ()));
                           set_of_unchecked_files1))))) uu____58032
         in
      FStar_All.pipe_right keys uu____58021  in
    let uu____58592 =
      let uu____58603 =
        let uu____58607 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____58607
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____58603
        (fun l  ->
           let uu____58644 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____58644))
       in
    match uu____58592 with
    | (all_fst_files,all_unchecked_fst_files) ->
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____58702 = FStar_Options.should_extract mname  in
                  if uu____58702
                  then
                    let uu____58705 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____58705
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____58732 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____58732));
          sort_output_files krml_file_map  in
        let rec make_transitive f =
          let uu____58751 =
            let uu____58763 = FStar_Util.smap_try_find transitive_krml f  in
            FStar_Util.must uu____58763  in
          match uu____58751 with
          | (exe,deps1,seen) ->
              if seen
              then (exe, deps1)
              else
                (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                 (let deps2 =
                    let uu____58857 =
                      let uu____58861 =
                        FStar_List.map
                          (fun dep1  ->
                             let uu____58877 = make_transitive dep1  in
                             match uu____58877 with
                             | (uu____58889,deps2) -> dep1 :: deps2) deps1
                         in
                      FStar_List.flatten uu____58861  in
                    FStar_List.unique uu____58857  in
                  FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                  (exe, deps2)))
           in
        ((let uu____58925 = FStar_Util.smap_keys transitive_krml  in
          FStar_List.iter
            (fun f  ->
               let uu____58950 = make_transitive f  in
               match uu____58950 with
               | (exe,deps1) ->
                   let deps2 =
                     let uu____58971 = FStar_List.unique (f :: deps1)  in
                     FStar_String.concat " " uu____58971  in
                   let wasm =
                     let uu____58980 =
                       FStar_Util.substring exe (Prims.parse_int "0")
                         ((FStar_String.length exe) - (Prims.parse_int "4"))
                        in
                     FStar_String.op_Hat uu____58980 ".wasm"  in
                   (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                    FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____58925);
         (let uu____58989 =
            let uu____58991 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58991 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____58989);
         (let uu____59010 =
            let uu____59012 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____59012 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n"
            uu____59010);
         (let uu____59031 =
            let uu____59033 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____59033 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____59031);
         (let uu____59051 =
            let uu____59053 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____59053 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____59051))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____59077 = FStar_Options.dep ()  in
    match uu____59077 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____59089 ->
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
         fun uu____59144  ->
           fun s  ->
             match uu____59144 with
             | (v0,v1) ->
                 let uu____59173 =
                   let uu____59175 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____59175  in
                 FStar_String.op_Hat s uu____59173) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____59196 =
        let uu____59198 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____59198  in
      has_interface deps.file_system_map uu____59196
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____59214 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____59214  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____59225 =
                   let uu____59227 = module_name_of_file f  in
                   FStar_String.lowercase uu____59227  in
                 uu____59225 = m)))
  