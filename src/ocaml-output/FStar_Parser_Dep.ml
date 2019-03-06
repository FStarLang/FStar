open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____46639 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____46650 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____46661 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____46684 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____46695 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____46706 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____46717 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____46728 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____46776 =
             (l > lext) &&
               (let uu____46779 = FStar_String.substring f (l - lext) lext
                   in
                uu____46779 = ext)
              in
           if uu____46776
           then
             let uu____46786 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____46786
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____46793 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____46793 with
    | (FStar_Pervasives_Native.Some m)::uu____46807 ->
        FStar_Pervasives_Native.Some m
    | uu____46819 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46836 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____46836 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46850 = is_interface f  in Prims.op_Negation uu____46850
  
let list_of_option :
  'Auu____46857 .
    'Auu____46857 FStar_Pervasives_Native.option -> 'Auu____46857 Prims.list
  =
  fun uu___423_46866  ->
    match uu___423_46866 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____46875 .
    ('Auu____46875 FStar_Pervasives_Native.option * 'Auu____46875
      FStar_Pervasives_Native.option) -> 'Auu____46875 Prims.list
  =
  fun uu____46890  ->
    match uu____46890 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46918 =
      let uu____46922 = FStar_Util.basename f  in
      check_and_strip_suffix uu____46922  in
    match uu____46918 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____46929 =
          let uu____46935 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____46935)  in
        FStar_Errors.raise_err uu____46929
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46949 = module_name_of_file f  in
    FStar_String.lowercase uu____46949
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____46962 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____46962 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____46965 ->
        let uu____46968 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____46968
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____47008 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____47032 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____47056 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____47080 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_47099  ->
    match uu___424_47099 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____47118 . unit -> 'Auu____47118 Prims.list =
  fun uu____47121  -> [] 
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
  fun uu____47463  ->
    fun k  -> match uu____47463 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____47485  ->
    fun k  ->
      fun v1  ->
        match uu____47485 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____47500  ->
    match uu____47500 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____47512  ->
    let uu____47513 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____47513
  
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
  let uu____47571 = deps_empty ()  in
  let uu____47572 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____47584 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____47571 uu____47572 [] [] [] uu____47584 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_47597  ->
    match uu___425_47597 with
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
      let uu____47626 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47626 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____47653) ->
          let uu____47675 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____47675
      | FStar_Pervasives_Native.Some
          (uu____47678,FStar_Pervasives_Native.Some fn) ->
          let uu____47701 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____47701
      | uu____47704 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47737 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47737 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____47764) ->
          FStar_Pervasives_Native.Some iface
      | uu____47787 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47820 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47820 with
      | FStar_Pervasives_Native.Some
          (uu____47846,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____47870 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____47899 = interface_of file_system_map key  in
      FStar_Option.isSome uu____47899
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47919 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____47919
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____47946 =
        let uu____47948 = FStar_Options.lax ()  in
        if uu____47948 then ".checked.lax" else ".checked"  in
      FStar_String.op_Hat fn uu____47946  in
    let uu____47956 =
      let uu____47960 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____47960  in
    match uu____47956 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____47981 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____47981
        then
          let uu____47992 =
            let uu____47998 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____47998)
             in
          FStar_Errors.raise_err uu____47992
        else
          (let uu____48010 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____48010, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____48024 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____48024 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____48060 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____48060 FStar_Util.must
  
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
                      (let uu____48114 = lowercase_module_name fn  in
                       key = uu____48114)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____48133 = interface_of file_system_map key  in
              (match uu____48133 with
               | FStar_Pervasives_Native.None  ->
                   let uu____48140 =
                     let uu____48146 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____48146)  in
                   FStar_Errors.raise_err uu____48140
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____48156 =
                (cmd_line_has_impl key) &&
                  (let uu____48159 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____48159)
                 in
              if uu____48156
              then
                let uu____48166 = FStar_Options.expose_interfaces ()  in
                (if uu____48166
                 then
                   let uu____48170 =
                     let uu____48172 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____48172  in
                   maybe_use_cache_of uu____48170
                 else
                   (let uu____48179 =
                      let uu____48185 =
                        let uu____48187 =
                          let uu____48189 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____48189  in
                        let uu____48194 =
                          let uu____48196 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____48196  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____48187 uu____48194
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____48185)
                       in
                    FStar_Errors.raise_err uu____48179))
              else
                (let uu____48206 =
                   let uu____48208 = interface_of file_system_map key  in
                   FStar_Option.get uu____48208  in
                 maybe_use_cache_of uu____48206)
          | PreferInterface key ->
              let uu____48215 = implementation_of file_system_map key  in
              (match uu____48215 with
               | FStar_Pervasives_Native.None  ->
                   let uu____48221 =
                     let uu____48227 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____48227)
                      in
                   FStar_Errors.raise_err uu____48221
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____48237 = implementation_of file_system_map key  in
              (match uu____48237 with
               | FStar_Pervasives_Native.None  ->
                   let uu____48243 =
                     let uu____48249 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____48249)
                      in
                   FStar_Errors.raise_err uu____48243
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____48259 = implementation_of file_system_map key  in
              (match uu____48259 with
               | FStar_Pervasives_Native.None  ->
                   let uu____48265 =
                     let uu____48271 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____48271)
                      in
                   FStar_Errors.raise_err uu____48265
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
          let uu____48332 = deps_try_find deps fn  in
          match uu____48332 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____48340;_} ->
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
    (let uu____48354 =
       let uu____48356 =
         let uu____48358 =
           let uu____48360 =
             let uu____48364 =
               let uu____48368 = deps_keys graph  in
               FStar_List.unique uu____48368  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____48382 =
                      let uu____48383 = deps_try_find graph k  in
                      FStar_Util.must uu____48383  in
                    uu____48382.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____48404 =
                      let uu____48406 = lowercase_module_name k  in
                      r uu____48406  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____48404
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____48364
              in
           FStar_String.concat "\n" uu____48360  in
         FStar_String.op_Hat uu____48358 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____48356  in
     FStar_Util.write_file "dep.graph" uu____48354)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____48427  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____48453 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____48453  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____48493 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____48493
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____48530 =
              let uu____48536 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____48536)  in
            FStar_Errors.raise_err uu____48530)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____48599 = FStar_Util.smap_try_find map1 key  in
      match uu____48599 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____48646 = is_interface full_path  in
          if uu____48646
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____48695 = is_interface full_path  in
          if uu____48695
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____48737 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____48755  ->
          match uu____48755 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____48737);
    FStar_List.iter
      (fun f  ->
         let uu____48774 = lowercase_module_name f  in
         add_entry uu____48774 f) filenames;
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
        (let uu____48806 =
           let uu____48810 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____48810  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____48846 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____48846  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____48806);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____48966 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____48966 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____48989 = string_of_lid l last1  in
      FStar_String.lowercase uu____48989
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____48998 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____48998
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____49020 =
        let uu____49022 =
          let uu____49024 =
            let uu____49026 =
              let uu____49030 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____49030  in
            FStar_Util.must uu____49026  in
          FStar_String.lowercase uu____49024  in
        uu____49022 <> k'  in
      if uu____49020
      then
        let uu____49035 = FStar_Ident.range_of_lid lid  in
        let uu____49036 =
          let uu____49042 =
            let uu____49044 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____49044 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____49042)  in
        FStar_Errors.log_issue uu____49035 uu____49036
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____49060 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____49082 = FStar_Options.prims_basename ()  in
      let uu____49084 =
        let uu____49088 = FStar_Options.pervasives_basename ()  in
        let uu____49090 =
          let uu____49094 = FStar_Options.pervasives_native_basename ()  in
          [uu____49094]  in
        uu____49088 :: uu____49090  in
      uu____49082 :: uu____49084  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____49137 =
         let uu____49140 = lowercase_module_name full_filename  in
         namespace_of_module uu____49140  in
       match uu____49137 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____49179 -> d = d'
  
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
        let uu____49219 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____49219
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____49254 =
             let uu____49255 = is_interface filename  in
             if uu____49255
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____49377 =
               let uu____49379 =
                 let uu____49381 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____49381  in
               Prims.op_Negation uu____49379  in
             if uu____49377
             then
               let uu____49408 =
                 let uu____49411 = FStar_ST.op_Bang deps1  in d ::
                   uu____49411
                  in
               FStar_ST.op_Colon_Equals deps1 uu____49408
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____49508 =
               resolve_module_name original_or_working_map key  in
             match uu____49508 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____49518 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____49518
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____49524 -> false  in
           let record_open_module let_open lid =
             let uu____49543 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____49543
             then true
             else
               (if let_open
                then
                  (let uu____49552 = FStar_Ident.range_of_lid lid  in
                   let uu____49553 =
                     let uu____49559 =
                       let uu____49561 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____49561
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____49559)
                      in
                   FStar_Errors.log_issue uu____49552 uu____49553)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____49581 = FStar_Ident.range_of_lid lid  in
               let uu____49582 =
                 let uu____49588 =
                   let uu____49590 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____49590
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____49588)
                  in
               FStar_Errors.log_issue uu____49581 uu____49582
             else ()  in
           let record_open let_open lid =
             let uu____49610 = record_open_module let_open lid  in
             if uu____49610
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____49627 =
             match uu____49627 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____49634 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____49651 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____49651  in
             let alias = lowercase_join_longident lid true  in
             let uu____49656 = FStar_Util.smap_try_find original_map alias
                in
             match uu____49656 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____49724 = FStar_Ident.range_of_lid lid  in
                   let uu____49725 =
                     let uu____49731 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____49731)
                      in
                   FStar_Errors.log_issue uu____49724 uu____49725);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____49742 = add_dependence_edge working_map module_name
                in
             if uu____49742
             then ()
             else
               (let uu____49747 = FStar_Options.debug_any ()  in
                if uu____49747
                then
                  let uu____49750 = FStar_Ident.range_of_lid module_name  in
                  let uu____49751 =
                    let uu____49757 =
                      let uu____49759 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____49759
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____49757)
                     in
                  FStar_Errors.log_issue uu____49750 uu____49751
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____49771 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_49899 =
              match uu___426_49899 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49910 =
                        let uu____49912 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49912
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____49918) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49929 =
                        let uu____49931 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49931
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
                  let uu____49953 =
                    let uu____49954 = lowercase_join_longident lid true  in
                    FriendImplementation uu____49954  in
                  add_dep deps uu____49953
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____49959 = record_module_alias ident lid  in
                  if uu____49959
                  then
                    let uu____49962 =
                      let uu____49963 = lowercase_join_longident lid true  in
                      dep_edge uu____49963  in
                    add_dep deps uu____49962
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____49968,patterms) ->
                  FStar_List.iter
                    (fun uu____49990  ->
                       match uu____49990 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____49999,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____50005,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____50007;
                    FStar_Parser_AST.mdest = uu____50008;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____50010;
                    FStar_Parser_AST.mdest = uu____50011;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____50013,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____50015;
                    FStar_Parser_AST.mdest = uu____50016;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____50020,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____50059  ->
                           match uu____50059 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____50072,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____50079 -> ()
              | FStar_Parser_AST.Pragma uu____50080 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____50083 =
                      let uu____50085 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____50085 > (Prims.parse_int "1")  in
                    if uu____50083
                    then
                      let uu____50110 =
                        let uu____50116 =
                          let uu____50118 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____50118
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____50116)
                         in
                      let uu____50123 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____50110 uu____50123
                    else ()))
            
            and collect_tycon uu___427_50126 =
              match uu___427_50126 with
              | FStar_Parser_AST.TyconAbstract (uu____50127,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____50139,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____50153,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____50199  ->
                        match uu____50199 with
                        | (uu____50208,t,uu____50210) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____50215,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____50277  ->
                        match uu____50277 with
                        | (uu____50291,t,uu____50293,uu____50294) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_50305 =
              match uu___428_50305 with
              | FStar_Parser_AST.DefineEffect (uu____50306,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____50320,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____50333,t);
                   FStar_Parser_AST.brange = uu____50335;
                   FStar_Parser_AST.blevel = uu____50336;
                   FStar_Parser_AST.aqual = uu____50337;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____50340,t);
                   FStar_Parser_AST.brange = uu____50342;
                   FStar_Parser_AST.blevel = uu____50343;
                   FStar_Parser_AST.aqual = uu____50344;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____50348;
                   FStar_Parser_AST.blevel = uu____50349;
                   FStar_Parser_AST.aqual = uu____50350;_} -> collect_term t
               | uu____50353 -> ())
            
            and collect_aqual uu___429_50354 =
              match uu___429_50354 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____50358 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_50362 =
              match uu___430_50362 with
              | FStar_Const.Const_int
                  (uu____50363,FStar_Pervasives_Native.Some
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
                  let uu____50390 =
                    let uu____50391 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____50391  in
                  add_dep deps uu____50390
              | FStar_Const.Const_char uu____50394 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____50397 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____50399 -> ()
            
            and collect_term' uu___433_50400 =
              match uu___433_50400 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____50409 =
                      let uu____50411 = FStar_Ident.text_of_id s  in
                      uu____50411 = "@"  in
                    if uu____50409
                    then
                      let uu____50416 =
                        let uu____50417 =
                          let uu____50418 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____50418
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____50417  in
                      collect_term' uu____50416
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____50422 -> ()
              | FStar_Parser_AST.Uvar uu____50423 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____50426) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____50451  ->
                        match uu____50451 with
                        | (t,uu____50457) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____50467) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____50469,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____50519  ->
                        match uu____50519 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____50548 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____50558,t1,t2) ->
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
                     (fun uu____50654  ->
                        match uu____50654 with
                        | (uu____50659,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____50662) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_50691  ->
                        match uu___431_50691 with
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
              | FStar_Parser_AST.NamedTyp (uu____50739,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____50743) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____50751) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____50759,uu____50760) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____50766) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____50780 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____50780);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_50790  ->
                        match uu___432_50790 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_50800 =
              match uu___434_50800 with
              | FStar_Parser_AST.PatVar (uu____50801,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____50807,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____50816 -> ()
              | FStar_Parser_AST.PatConst uu____50817 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____50825 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____50833) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____50854  ->
                       match uu____50854 with
                       | (uu____50859,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____50904 =
              match uu____50904 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____50922 = FStar_Parser_Driver.parse_file filename  in
            match uu____50922 with
            | (ast,uu____50935) ->
                let mname = lowercase_module_name filename  in
                ((let uu____50953 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____50953
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____50959 = FStar_ST.op_Bang deps  in
                  let uu____50985 = FStar_ST.op_Bang mo_roots  in
                  let uu____51011 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____50959;
                    additional_roots = uu____50985;
                    has_inline_for_extraction = uu____51011
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____51050 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____51050 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____51172 = dep_graph  in
    match uu____51172 with
    | Deps g -> let uu____51176 = FStar_Util.smap_copy g  in Deps uu____51176
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____51321 filename =
              match uu____51321 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____51362 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____51362  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____51393 = FStar_Options.debug_any ()  in
                         if uu____51393
                         then
                           let uu____51396 =
                             let uu____51398 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____51398  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____51396
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1245_51409 = dep_node  in
                           { edges = (uu___1245_51409.edges); color = Gray });
                        (let uu____51410 =
                           let uu____51421 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____51421
                            in
                         match uu____51410 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1251_51457 = dep_node  in
                                 {
                                   edges = (uu___1251_51457.edges);
                                   color = Black
                                 });
                              (let uu____51459 = FStar_Options.debug_any ()
                                  in
                               if uu____51459
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____51465 =
                                 let uu____51469 =
                                   FStar_List.collect
                                     (fun uu___435_51476  ->
                                        match uu___435_51476 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____51469 all_friends1
                                  in
                               (uu____51465, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____51542 = FStar_Options.debug_any ()  in
             if uu____51542
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____51571 = deps  in
               match uu____51571 with
               | Deps dg ->
                   let uu____51575 = deps_empty ()  in
                   (match uu____51575 with
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
                                  | uu____51625 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____51633  ->
                                  let uu____51635 =
                                    let uu___1286_51636 = dep_node  in
                                    let uu____51637 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____51637; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____51635) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____51639 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____51639
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____51644 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____51644 with
             | (friends,all_files_0) ->
                 ((let uu____51687 = FStar_Options.debug_any ()  in
                   if uu____51687
                   then
                     let uu____51690 =
                       let uu____51692 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____51692  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____51690
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____51711 =
                     (let uu____51723 = FStar_Options.debug_any ()  in
                      if uu____51723
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____51711 with
                   | (uu____51746,all_files) ->
                       ((let uu____51761 = FStar_Options.debug_any ()  in
                         if uu____51761
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____51768 = FStar_ST.op_Bang widened  in
                         (all_files, uu____51768))))))
  
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
                let uu____51854 = FStar_Options.find_file fn  in
                match uu____51854 with
                | FStar_Pervasives_Native.None  ->
                    let uu____51860 =
                      let uu____51866 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____51866)
                       in
                    FStar_Errors.raise_err uu____51860
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____51896 =
          let uu____51900 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____51900  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____51896  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____51967 =
          let uu____51969 = deps_try_find dep_graph file_name  in
          uu____51969 = FStar_Pervasives_Native.None  in
        if uu____51967
        then
          let uu____51975 =
            let uu____51987 =
              let uu____52001 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____52001 file_name  in
            match uu____51987 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____51975 with
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
                  let uu____52145 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____52145
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____52153 = FStar_List.unique deps1  in
                  { edges = uu____52153; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____52155 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____52155)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____52195 =
            let uu____52201 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____52201)  in
          FStar_Errors.raise_err uu____52195)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____52238 = deps_try_find dep_graph1 filename  in
             match uu____52238 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____52242 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____52242
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____52256 =
                           implementation_of file_system_map f  in
                         (match uu____52256 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____52267 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____52273 =
                           implementation_of file_system_map f  in
                         (match uu____52273 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____52284 -> [x; UseImplementation f])
                     | uu____52288 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1370_52291 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____52293 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____52293);
                deps_add_dep dep_graph1 filename
                  (let uu___1375_52303 = node  in
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
        let uu____52347 =
          let uu____52356 =
            let uu____52358 = FStar_Options.codegen ()  in
            uu____52358 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____52356
           in
        match uu____52347 with
        | (all_files,uu____52371) ->
            ((let uu____52381 = FStar_Options.debug_any ()  in
              if uu____52381
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
          let uu____52451 = FStar_Options.find_file fn  in
          match uu____52451 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____52459 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____52473 = FStar_Options.debug_any ()  in
           if uu____52473
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____52492 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____52492
          then
            let uu____52503 =
              let uu____52510 =
                let uu____52512 =
                  let uu____52514 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____52514  in
                digest_of_file1 uu____52512  in
              ("interface", uu____52510)  in
            [uu____52503]
          else []  in
        let binary_deps =
          let uu____52546 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____52546
            (FStar_List.filter
               (fun fn2  ->
                  let uu____52561 =
                    (is_interface fn2) &&
                      (let uu____52564 = lowercase_module_name fn2  in
                       uu____52564 = module_name)
                     in
                  Prims.op_Negation uu____52561))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____52580 = lowercase_module_name fn11  in
                 let uu____52582 = lowercase_module_name fn2  in
                 FStar_String.compare uu____52580 uu____52582) binary_deps
           in
        let rec hash_deps out uu___436_52618 =
          match uu___436_52618 with
          | [] ->
              FStar_Util.Inr
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____52685 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____52685
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____52706 = FStar_Options.debug_any ()  in
                     if uu____52706
                     then
                       let uu____52709 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____52709
                     else ());
                    (let uu____52714 =
                       FStar_Util.format1 "cache file %s does not exist"
                         cache_fn
                        in
                     FStar_Util.Inl uu____52714))
               | FStar_Pervasives_Native.Some dig ->
                   let uu____52729 =
                     let uu____52738 =
                       let uu____52745 = lowercase_module_name fn2  in
                       (uu____52745, dig)  in
                     uu____52738 :: out  in
                   hash_deps uu____52729 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____52785 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____52811  ->
              match uu____52811 with
              | (m,d) ->
                  let uu____52825 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____52825))
       in
    FStar_All.pipe_right uu____52785 (FStar_String.concat "\n")
  
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
              let uu____52860 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____52860 FStar_Option.get  in
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
    let uu____52889 = deps.dep_graph  in
    match uu____52889 with
    | Deps deps1 ->
        let uu____52893 =
          let uu____52895 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____52913 =
                       let uu____52915 =
                         let uu____52917 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____52917
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____52915
                        in
                     uu____52913 :: out) []
             in
          FStar_All.pipe_right uu____52895 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____52893 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____52989 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____52989) ||
          (let uu____52996 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____52996)
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
            let uu____53039 =
              let uu____53043 = FStar_ST.op_Bang order  in ml_file ::
                uu____53043
               in
            FStar_ST.op_Colon_Equals order uu____53039
         in
      let rec aux uu___437_53106 =
        match uu___437_53106 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____53134 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____53134 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____53137 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____53137
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____53141;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____53150 = should_visit lc_module_name  in
              if uu____53150
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____53158 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____53158);
                 (let uu____53163 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____53163);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____53175 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____53175)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____53227 =
          let uu____53229 =
            let uu____53233 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____53233  in
          FStar_Option.get uu____53229  in
        FStar_Util.replace_chars uu____53227 46 "_"  in
      let uu____53238 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____53238  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____53260 = output_file ".ml" f  in norm_path uu____53260  in
    let output_krml_file f =
      let uu____53272 = output_file ".krml" f  in norm_path uu____53272  in
    let output_cmx_file f =
      let uu____53284 = output_file ".cmx" f  in norm_path uu____53284  in
    let cache_file f =
      let uu____53301 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____53301
        (fun uu____53330  ->
           match uu____53330 with | (f1,b) -> ((norm_path f1), b))
       in
    let set_of_unchecked_files =
      let uu____53355 =
        let uu____53366 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____53403 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____53403 FStar_Option.get  in
               let iface_deps =
                 let uu____53413 = is_interface file_name  in
                 if uu____53413
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____53424 =
                      let uu____53428 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____53428  in
                    match uu____53424 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____53440 =
                          let uu____53443 =
                            let uu____53444 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____53444  in
                          uu____53443.edges  in
                        FStar_Pervasives_Native.Some uu____53440)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____53461 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____53461))
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
               let uu____53520 = cache_file file_name  in
               match uu____53520 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let uu____53549 =
                       let uu____53558 = FStar_Options.cmi ()  in
                       if uu____53558
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
                          let uu____53606 =
                            FStar_Util.remove_dups
                              (fun x  -> fun y  -> x = y)
                              (FStar_List.append fst_files
                                 fst_files_from_iface)
                             in
                          (uu____53606, false))
                        in
                     match uu____53549 with
                     | (all_fst_files_dep,widened) ->
                         let all_checked_fst_dep_files =
                           FStar_All.pipe_right all_fst_files_dep
                             (FStar_List.map
                                (fun f  ->
                                   let uu____53653 =
                                     FStar_All.pipe_right f cache_file  in
                                   FStar_All.pipe_right uu____53653
                                     FStar_Pervasives_Native.fst))
                            in
                         ((let uu____53677 = is_implementation file_name  in
                           if uu____53677
                           then
                             ((let uu____53681 =
                                 (FStar_Options.cmi ()) && widened  in
                               if uu____53681
                               then
                                 ((let uu____53685 = output_ml_file file_name
                                      in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____53685 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files));
                                  (let uu____53689 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____53689 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)))
                               else
                                 ((let uu____53696 = output_ml_file file_name
                                      in
                                   FStar_Util.print2 "%s: %s \n\n"
                                     uu____53696 cache_file_name1);
                                  (let uu____53699 =
                                     output_krml_file file_name  in
                                   FStar_Util.print2 "%s: %s\n\n" uu____53699
                                     cache_file_name1)));
                              (let cmx_files =
                                 let extracted_fst_files =
                                   FStar_All.pipe_right all_fst_files_dep
                                     (FStar_List.filter
                                        (fun df  ->
                                           (let uu____53724 =
                                              lowercase_module_name df  in
                                            let uu____53726 =
                                              lowercase_module_name file_name
                                               in
                                            uu____53724 <> uu____53726) &&
                                             (let uu____53730 =
                                                lowercase_module_name df  in
                                              FStar_Options.should_extract
                                                uu____53730)))
                                    in
                                 FStar_All.pipe_right extracted_fst_files
                                   (FStar_List.map output_cmx_file)
                                  in
                               let uu____53740 =
                                 let uu____53742 =
                                   lowercase_module_name file_name  in
                                 FStar_Options.should_extract uu____53742  in
                               if uu____53740
                               then
                                 let uu____53745 = output_cmx_file file_name
                                    in
                                 let uu____53747 = output_ml_file file_name
                                    in
                                 FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                   uu____53745 uu____53747
                                   (FStar_String.concat "\\\n\t" cmx_files)
                               else ()))
                           else
                             (let uu____53755 =
                                (let uu____53759 =
                                   let uu____53761 =
                                     lowercase_module_name file_name  in
                                   has_implementation deps.file_system_map
                                     uu____53761
                                    in
                                 Prims.op_Negation uu____53759) &&
                                  (is_interface file_name)
                                 in
                              if uu____53755
                              then
                                let uu____53764 =
                                  (FStar_Options.cmi ()) && widened  in
                                (if uu____53764
                                 then
                                   let uu____53767 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____53767 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)
                                 else
                                   (let uu____53773 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____53773 cache_file_name1))
                              else ()));
                          set_of_unchecked_files1)))) uu____53366
         in
      FStar_All.pipe_right keys uu____53355  in
    let uu____53784 =
      let uu____53795 =
        let uu____53799 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____53799
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____53795
        (fun l  ->
           let uu____53836 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____53836))
       in
    match uu____53784 with
    | (all_fst_files,all_unchecked_fst_files) ->
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____53894 = FStar_Options.should_extract mname  in
                  if uu____53894
                  then
                    let uu____53897 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____53897
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____53924 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____53924));
          sort_output_files krml_file_map  in
        ((let uu____53928 =
            let uu____53930 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53930 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____53928);
         (let uu____53949 =
            let uu____53951 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53951 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n"
            uu____53949);
         (let uu____53970 =
            let uu____53972 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53972 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____53970);
         (let uu____53990 =
            let uu____53992 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53992 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____53990))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____54016 = FStar_Options.dep ()  in
    match uu____54016 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____54028 ->
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
         fun uu____54083  ->
           fun s  ->
             match uu____54083 with
             | (v0,v1) ->
                 let uu____54112 =
                   let uu____54114 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____54114  in
                 FStar_String.op_Hat s uu____54112) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____54135 =
        let uu____54137 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____54137  in
      has_interface deps.file_system_map uu____54135
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____54153 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____54153  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____54164 =
                   let uu____54166 = module_name_of_file f  in
                   FStar_String.lowercase uu____54166  in
                 uu____54164 = m)))
  