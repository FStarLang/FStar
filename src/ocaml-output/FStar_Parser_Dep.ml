open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____50429 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____50440 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____50451 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____50474 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____50485 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____50496 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____50507 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____50518 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____50566 =
             (l > lext) &&
               (let uu____50579 = FStar_String.substring f (l - lext) lext
                   in
                uu____50579 = ext)
              in
           if uu____50566
           then
             let uu____50600 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____50600
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____50617 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____50617 with
    | (FStar_Pervasives_Native.Some m)::uu____50631 ->
        FStar_Pervasives_Native.Some m
    | uu____50643 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____50660 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____50660 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____50674 = is_interface f  in Prims.op_Negation uu____50674
  
let list_of_option :
  'Auu____50681 .
    'Auu____50681 FStar_Pervasives_Native.option -> 'Auu____50681 Prims.list
  =
  fun uu___423_50690  ->
    match uu___423_50690 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____50699 .
    ('Auu____50699 FStar_Pervasives_Native.option * 'Auu____50699
      FStar_Pervasives_Native.option) -> 'Auu____50699 Prims.list
  =
  fun uu____50714  ->
    match uu____50714 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____50742 =
      let uu____50746 = FStar_Util.basename f  in
      check_and_strip_suffix uu____50746  in
    match uu____50742 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____50753 =
          let uu____50759 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____50759)  in
        FStar_Errors.raise_err uu____50753
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____50773 = module_name_of_file f  in
    FStar_String.lowercase uu____50773
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____50786 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____50786 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____50789 ->
        let uu____50792 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____50792
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____50834 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____50858 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____50882 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____50906 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_50925  ->
    match uu___424_50925 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____50944 . unit -> 'Auu____50944 Prims.list =
  fun uu____50947  -> [] 
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
  fun uu____51289  ->
    fun k  -> match uu____51289 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____51311  ->
    fun k  ->
      fun v1  ->
        match uu____51311 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____51326  ->
    match uu____51326 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____51338  ->
    let uu____51339 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____51339
  
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
  let uu____51397 = deps_empty ()  in
  let uu____51398 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____51410 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____51397 uu____51398 [] [] [] uu____51410 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_51423  ->
    match uu___425_51423 with
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
      let uu____51452 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51452 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____51479) ->
          let uu____51501 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____51501
      | FStar_Pervasives_Native.Some
          (uu____51504,FStar_Pervasives_Native.Some fn) ->
          let uu____51527 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____51527
      | uu____51530 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51563 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51563 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____51590) ->
          FStar_Pervasives_Native.Some iface
      | uu____51613 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51646 = FStar_Util.smap_try_find file_system_map key  in
      match uu____51646 with
      | FStar_Pervasives_Native.Some
          (uu____51672,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____51696 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____51725 = interface_of file_system_map key  in
      FStar_Option.isSome uu____51725
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____51745 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____51745
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____51772 =
        let uu____51774 = FStar_Options.lax ()  in
        if uu____51774 then ".checked.lax" else ".checked"  in
      FStar_String.op_Hat fn uu____51772  in
    let uu____51782 =
      let uu____51786 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____51786  in
    match uu____51782 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____51807 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____51807
        then
          let uu____51818 =
            let uu____51824 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____51824)
             in
          FStar_Errors.raise_err uu____51818
        else
          (let uu____51836 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____51836, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____51850 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____51850 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____51886 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____51886 FStar_Util.must
  
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
                      (let uu____51940 = lowercase_module_name fn  in
                       key = uu____51940)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____51959 = interface_of file_system_map key  in
              (match uu____51959 with
               | FStar_Pervasives_Native.None  ->
                   let uu____51966 =
                     let uu____51972 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____51972)  in
                   FStar_Errors.raise_err uu____51966
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____51982 =
                (cmd_line_has_impl key) &&
                  (let uu____51985 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____51985)
                 in
              if uu____51982
              then
                let uu____51992 = FStar_Options.expose_interfaces ()  in
                (if uu____51992
                 then
                   let uu____51996 =
                     let uu____51998 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____51998  in
                   maybe_use_cache_of uu____51996
                 else
                   (let uu____52005 =
                      let uu____52011 =
                        let uu____52013 =
                          let uu____52015 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____52015  in
                        let uu____52020 =
                          let uu____52022 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____52022  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____52013 uu____52020
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____52011)
                       in
                    FStar_Errors.raise_err uu____52005))
              else
                (let uu____52032 =
                   let uu____52034 = interface_of file_system_map key  in
                   FStar_Option.get uu____52034  in
                 maybe_use_cache_of uu____52032)
          | PreferInterface key ->
              let uu____52041 = implementation_of file_system_map key  in
              (match uu____52041 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52047 =
                     let uu____52053 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52053)
                      in
                   FStar_Errors.raise_err uu____52047
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____52063 = implementation_of file_system_map key  in
              (match uu____52063 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52069 =
                     let uu____52075 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52075)
                      in
                   FStar_Errors.raise_err uu____52069
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____52085 = implementation_of file_system_map key  in
              (match uu____52085 with
               | FStar_Pervasives_Native.None  ->
                   let uu____52091 =
                     let uu____52097 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____52097)
                      in
                   FStar_Errors.raise_err uu____52091
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
          let uu____52158 = deps_try_find deps fn  in
          match uu____52158 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____52166;_} ->
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
    (let uu____52180 =
       let uu____52182 =
         let uu____52184 =
           let uu____52186 =
             let uu____52190 =
               let uu____52194 = deps_keys graph  in
               FStar_List.unique uu____52194  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____52208 =
                      let uu____52209 = deps_try_find graph k  in
                      FStar_Util.must uu____52209  in
                    uu____52208.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____52230 =
                      let uu____52232 = lowercase_module_name k  in
                      r uu____52232  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____52230
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____52190
              in
           FStar_String.concat "\n" uu____52186  in
         FStar_String.op_Hat uu____52184 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____52182  in
     FStar_Util.write_file "dep.graph" uu____52180)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____52253  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____52279 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____52279  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____52319 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____52319
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____52356 =
              let uu____52362 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____52362)  in
            FStar_Errors.raise_err uu____52356)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____52425 = FStar_Util.smap_try_find map1 key  in
      match uu____52425 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____52472 = is_interface full_path  in
          if uu____52472
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____52521 = is_interface full_path  in
          if uu____52521
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____52563 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____52581  ->
          match uu____52581 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____52563);
    FStar_List.iter
      (fun f  ->
         let uu____52600 = lowercase_module_name f  in
         add_entry uu____52600 f) filenames;
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
        (let uu____52632 =
           let uu____52636 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____52636  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____52672 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____52672  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____52632);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____52836 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____52836 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____52859 = string_of_lid l last1  in
      FStar_String.lowercase uu____52859
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____52868 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____52868
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____52890 =
        let uu____52892 =
          let uu____52894 =
            let uu____52896 =
              let uu____52900 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____52900  in
            FStar_Util.must uu____52896  in
          FStar_String.lowercase uu____52894  in
        uu____52892 <> k'  in
      if uu____52890
      then
        let uu____52905 = FStar_Ident.range_of_lid lid  in
        let uu____52906 =
          let uu____52912 =
            let uu____52914 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____52914 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____52912)  in
        FStar_Errors.log_issue uu____52905 uu____52906
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____52930 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____52952 = FStar_Options.prims_basename ()  in
      let uu____52954 =
        let uu____52958 = FStar_Options.pervasives_basename ()  in
        let uu____52960 =
          let uu____52964 = FStar_Options.pervasives_native_basename ()  in
          [uu____52964]  in
        uu____52958 :: uu____52960  in
      uu____52952 :: uu____52954  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____53007 =
         let uu____53010 = lowercase_module_name full_filename  in
         namespace_of_module uu____53010  in
       match uu____53007 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____53049 -> d = d'
  
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
        let uu____53089 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____53089
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____53124 =
             let uu____53125 = is_interface filename  in
             if uu____53125
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____53332 =
               let uu____53334 =
                 let uu____53336 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____53336  in
               Prims.op_Negation uu____53334  in
             if uu____53332
             then
               let uu____53405 =
                 let uu____53408 = FStar_ST.op_Bang deps1  in d ::
                   uu____53408
                  in
               FStar_ST.op_Colon_Equals deps1 uu____53405
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____53589 =
               resolve_module_name original_or_working_map key  in
             match uu____53589 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____53632 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____53632
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____53671 -> false  in
           let record_open_module let_open lid =
             let uu____53690 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____53690
             then true
             else
               (if let_open
                then
                  (let uu____53699 = FStar_Ident.range_of_lid lid  in
                   let uu____53700 =
                     let uu____53706 =
                       let uu____53708 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____53708
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____53706)
                      in
                   FStar_Errors.log_issue uu____53699 uu____53700)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____53728 = FStar_Ident.range_of_lid lid  in
               let uu____53729 =
                 let uu____53735 =
                   let uu____53737 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____53737
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____53735)
                  in
               FStar_Errors.log_issue uu____53728 uu____53729
             else ()  in
           let record_open let_open lid =
             let uu____53757 = record_open_module let_open lid  in
             if uu____53757
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____53774 =
             match uu____53774 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____53781 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____53798 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____53798  in
             let alias = lowercase_join_longident lid true  in
             let uu____53803 = FStar_Util.smap_try_find original_map alias
                in
             match uu____53803 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____53871 = FStar_Ident.range_of_lid lid  in
                   let uu____53872 =
                     let uu____53878 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____53878)
                      in
                   FStar_Errors.log_issue uu____53871 uu____53872);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____53889 = add_dependence_edge working_map module_name
                in
             if uu____53889
             then ()
             else
               (let uu____53894 = FStar_Options.debug_any ()  in
                if uu____53894
                then
                  let uu____53897 = FStar_Ident.range_of_lid module_name  in
                  let uu____53898 =
                    let uu____53904 =
                      let uu____53906 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____53906
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____53904)
                     in
                  FStar_Errors.log_issue uu____53897 uu____53898
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____53918 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_54046 =
              match uu___426_54046 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____54057 =
                        let uu____54059 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____54059
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____54065) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____54076 =
                        let uu____54078 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____54078
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
                  let uu____54100 =
                    let uu____54101 = lowercase_join_longident lid true  in
                    FriendImplementation uu____54101  in
                  add_dep deps uu____54100
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____54139 = record_module_alias ident lid  in
                  if uu____54139
                  then
                    let uu____54142 =
                      let uu____54143 = lowercase_join_longident lid true  in
                      dep_edge uu____54143  in
                    add_dep deps uu____54142
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____54181,patterms) ->
                  FStar_List.iter
                    (fun uu____54203  ->
                       match uu____54203 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____54212,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____54218,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54220;
                    FStar_Parser_AST.mdest = uu____54221;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54223;
                    FStar_Parser_AST.mdest = uu____54224;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____54226,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____54228;
                    FStar_Parser_AST.mdest = uu____54229;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____54233,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____54272  ->
                           match uu____54272 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____54285,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____54292 -> ()
              | FStar_Parser_AST.Pragma uu____54293 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____54329 =
                      let uu____54331 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____54331 > (Prims.parse_int "1")  in
                    if uu____54329
                    then
                      let uu____54378 =
                        let uu____54384 =
                          let uu____54386 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____54386
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____54384)
                         in
                      let uu____54391 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____54378 uu____54391
                    else ()))
            
            and collect_tycon uu___427_54394 =
              match uu___427_54394 with
              | FStar_Parser_AST.TyconAbstract (uu____54395,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____54407,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____54421,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____54467  ->
                        match uu____54467 with
                        | (uu____54476,t,uu____54478) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____54483,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____54545  ->
                        match uu____54545 with
                        | (uu____54559,t,uu____54561,uu____54562) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_54573 =
              match uu___428_54573 with
              | FStar_Parser_AST.DefineEffect (uu____54574,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____54588,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____54601,t);
                   FStar_Parser_AST.brange = uu____54603;
                   FStar_Parser_AST.blevel = uu____54604;
                   FStar_Parser_AST.aqual = uu____54605;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____54608,t);
                   FStar_Parser_AST.brange = uu____54610;
                   FStar_Parser_AST.blevel = uu____54611;
                   FStar_Parser_AST.aqual = uu____54612;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____54616;
                   FStar_Parser_AST.blevel = uu____54617;
                   FStar_Parser_AST.aqual = uu____54618;_} -> collect_term t
               | uu____54621 -> ())
            
            and collect_aqual uu___429_54622 =
              match uu___429_54622 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____54626 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_54630 =
              match uu___430_54630 with
              | FStar_Const.Const_int
                  (uu____54631,FStar_Pervasives_Native.Some
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
                  let uu____54658 =
                    let uu____54659 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____54659  in
                  add_dep deps uu____54658
              | FStar_Const.Const_char uu____54695 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____54731 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____54766 -> ()
            
            and collect_term' uu___433_54767 =
              match uu___433_54767 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____54776 =
                      let uu____54778 = FStar_Ident.text_of_id s  in
                      uu____54778 = "@"  in
                    if uu____54776
                    then
                      let uu____54783 =
                        let uu____54784 =
                          let uu____54785 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____54785
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____54784  in
                      collect_term' uu____54783
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____54789 -> ()
              | FStar_Parser_AST.Uvar uu____54790 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____54793) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (if (FStar_List.length termimps) = (Prims.parse_int "1")
                   then record_lid lid
                   else ();
                   FStar_List.iter
                     (fun uu____54827  ->
                        match uu____54827 with
                        | (t,uu____54833) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____54843) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____54845,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____54895  ->
                        match uu____54895 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____54924 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____54934,t1,t2) ->
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
                     (fun uu____55030  ->
                        match uu____55030 with
                        | (uu____55035,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____55038) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_55067  ->
                        match uu___431_55067 with
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
              | FStar_Parser_AST.NamedTyp (uu____55115,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____55119) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____55127) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____55135,uu____55136) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____55142) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____55156 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____55156);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_55166  ->
                        match uu___432_55166 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_55176 =
              match uu___434_55176 with
              | FStar_Parser_AST.PatVar (uu____55177,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____55183,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____55192 -> ()
              | FStar_Parser_AST.PatConst uu____55193 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____55201 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____55209) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____55230  ->
                       match uu____55230 with
                       | (uu____55235,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____55280 =
              match uu____55280 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____55298 = FStar_Parser_Driver.parse_file filename  in
            match uu____55298 with
            | (ast,uu____55311) ->
                let mname = lowercase_module_name filename  in
                ((let uu____55329 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____55329
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____55368 = FStar_ST.op_Bang deps  in
                  let uu____55416 = FStar_ST.op_Bang mo_roots  in
                  let uu____55464 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____55368;
                    additional_roots = uu____55416;
                    has_inline_for_extraction = uu____55464
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____55536 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____55536 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____55658 = dep_graph  in
    match uu____55658 with
    | Deps g -> let uu____55662 = FStar_Util.smap_copy g  in Deps uu____55662
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____55807 filename =
              match uu____55807 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____55848 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____55848  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____55879 = FStar_Options.debug_any ()  in
                         if uu____55879
                         then
                           let uu____55882 =
                             let uu____55884 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____55884  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____55882
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1246_55895 = dep_node  in
                           { edges = (uu___1246_55895.edges); color = Gray });
                        (let uu____55896 =
                           let uu____55907 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____55907
                            in
                         match uu____55896 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1252_55943 = dep_node  in
                                 {
                                   edges = (uu___1252_55943.edges);
                                   color = Black
                                 });
                              (let uu____55945 = FStar_Options.debug_any ()
                                  in
                               if uu____55945
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____55951 =
                                 let uu____55955 =
                                   FStar_List.collect
                                     (fun uu___435_55962  ->
                                        match uu___435_55962 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____55955 all_friends1
                                  in
                               (uu____55951, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____56028 = FStar_Options.debug_any ()  in
             if uu____56028
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____56057 = deps  in
               match uu____56057 with
               | Deps dg ->
                   let uu____56061 = deps_empty ()  in
                   (match uu____56061 with
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
                                  | uu____56133 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____56141  ->
                                  let uu____56143 =
                                    let uu___1287_56144 = dep_node  in
                                    let uu____56145 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____56145; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____56143) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____56147 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____56147
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____56152 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____56152 with
             | (friends,all_files_0) ->
                 ((let uu____56195 = FStar_Options.debug_any ()  in
                   if uu____56195
                   then
                     let uu____56198 =
                       let uu____56200 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____56200  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____56198
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____56219 =
                     (let uu____56231 = FStar_Options.debug_any ()  in
                      if uu____56231
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____56219 with
                   | (uu____56254,all_files) ->
                       ((let uu____56269 = FStar_Options.debug_any ()  in
                         if uu____56269
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____56276 = FStar_ST.op_Bang widened  in
                         (all_files, uu____56276))))))
  
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
                let uu____56384 = FStar_Options.find_file fn  in
                match uu____56384 with
                | FStar_Pervasives_Native.None  ->
                    let uu____56390 =
                      let uu____56396 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____56396)
                       in
                    FStar_Errors.raise_err uu____56390
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____56426 =
          let uu____56430 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____56430  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____56426  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____56541 =
          let uu____56543 = deps_try_find dep_graph file_name  in
          uu____56543 = FStar_Pervasives_Native.None  in
        if uu____56541
        then
          let uu____56549 =
            let uu____56561 =
              let uu____56575 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____56575 file_name  in
            match uu____56561 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____56549 with
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
                  let uu____56719 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____56719
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____56727 = FStar_List.unique deps1  in
                  { edges = uu____56727; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____56729 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____56729)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____56769 =
            let uu____56775 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____56775)  in
          FStar_Errors.raise_err uu____56769)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____56812 = deps_try_find dep_graph1 filename  in
             match uu____56812 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____56816 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____56816
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____56830 =
                           implementation_of file_system_map f  in
                         (match uu____56830 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____56841 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____56847 =
                           implementation_of file_system_map f  in
                         (match uu____56847 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____56858 -> [x; UseImplementation f])
                     | uu____56862 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1371_56865 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____56867 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____56867);
                deps_add_dep dep_graph1 filename
                  (let uu___1376_56877 = node  in
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
        let uu____56943 =
          let uu____56952 =
            let uu____56954 = FStar_Options.codegen ()  in
            uu____56954 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____56952
           in
        match uu____56943 with
        | (all_files,uu____56967) ->
            ((let uu____56977 = FStar_Options.debug_any ()  in
              if uu____56977
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
          let uu____57044 = FStar_Options.find_file fn  in
          match uu____57044 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____57052 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____57066 = FStar_Options.debug_any ()  in
           if uu____57066
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____57085 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____57085
          then
            let uu____57096 =
              let uu____57103 =
                let uu____57105 =
                  let uu____57107 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____57107  in
                digest_of_file1 uu____57105  in
              ("interface", uu____57103)  in
            [uu____57096]
          else []  in
        let binary_deps =
          let uu____57139 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____57139
            (FStar_List.filter
               (fun fn2  ->
                  let uu____57154 =
                    (is_interface fn2) &&
                      (let uu____57157 = lowercase_module_name fn2  in
                       uu____57157 = module_name)
                     in
                  Prims.op_Negation uu____57154))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____57173 = lowercase_module_name fn11  in
                 let uu____57175 = lowercase_module_name fn2  in
                 FStar_String.compare uu____57173 uu____57175) binary_deps
           in
        let rec hash_deps out uu___436_57208 =
          match uu___436_57208 with
          | [] ->
              FStar_Pervasives_Native.Some
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____57271 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____57271
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____57289 = FStar_Options.debug_any ()  in
                     if uu____57289
                     then
                       let uu____57292 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____57292
                     else ());
                    FStar_Pervasives_Native.None)
               | FStar_Pervasives_Native.Some dig ->
                   let uu____57308 =
                     let uu____57317 =
                       let uu____57324 = lowercase_module_name fn2  in
                       (uu____57324, dig)  in
                     uu____57317 :: out  in
                   hash_deps uu____57308 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____57364 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____57390  ->
              match uu____57390 with
              | (m,d) ->
                  let uu____57404 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____57404))
       in
    FStar_All.pipe_right uu____57364 (FStar_String.concat "\n")
  
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
              let uu____57439 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____57439 FStar_Option.get  in
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
    let uu____57468 = deps.dep_graph  in
    match uu____57468 with
    | Deps deps1 ->
        let uu____57472 =
          let uu____57474 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____57492 =
                       let uu____57494 =
                         let uu____57496 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____57496
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____57494
                        in
                     uu____57492 :: out) []
             in
          FStar_All.pipe_right uu____57474 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____57472 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____57568 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____57568) ||
          (let uu____57575 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____57575)
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
            let uu____57618 =
              let uu____57622 = FStar_ST.op_Bang order  in ml_file ::
                uu____57622
               in
            FStar_ST.op_Colon_Equals order uu____57618
         in
      let rec aux uu___437_57729 =
        match uu___437_57729 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____57757 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____57757 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____57760 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____57760
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____57764;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____57773 = should_visit lc_module_name  in
              if uu____57773
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____57781 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____57781);
                 (let uu____57786 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____57786);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____57798 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____57798)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____57872 =
          let uu____57874 =
            let uu____57878 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____57878  in
          FStar_Option.get uu____57874  in
        FStar_Util.replace_chars uu____57872 46 "_"  in
      let uu____57883 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____57883  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____57905 = output_file ".ml" f  in norm_path uu____57905  in
    let output_krml_file f =
      let uu____57917 = output_file ".krml" f  in norm_path uu____57917  in
    let output_cmx_file f =
      let uu____57929 = output_file ".cmx" f  in norm_path uu____57929  in
    let cache_file f =
      let uu____57946 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____57946
        (fun uu____57975  ->
           match uu____57975 with | (f1,b) -> ((norm_path f1), b))
       in
    let set_of_unchecked_files =
      let uu____58000 =
        let uu____58011 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____58048 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____58048 FStar_Option.get  in
               let iface_deps =
                 let uu____58058 = is_interface file_name  in
                 if uu____58058
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____58069 =
                      let uu____58073 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____58073  in
                    match uu____58069 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____58085 =
                          let uu____58088 =
                            let uu____58089 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____58089  in
                          uu____58088.edges  in
                        FStar_Pervasives_Native.Some uu____58085)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____58106 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____58106))
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
               let uu____58165 = cache_file file_name  in
               match uu____58165 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let uu____58194 =
                       let uu____58203 = FStar_Options.cmi ()  in
                       if uu____58203
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
                          let uu____58251 =
                            FStar_Util.remove_dups
                              (fun x  -> fun y  -> x = y)
                              (FStar_List.append fst_files
                                 fst_files_from_iface)
                             in
                          (uu____58251, false))
                        in
                     match uu____58194 with
                     | (all_fst_files_dep,widened) ->
                         let all_checked_fst_dep_files =
                           FStar_All.pipe_right all_fst_files_dep
                             (FStar_List.map
                                (fun f  ->
                                   let uu____58298 =
                                     FStar_All.pipe_right f cache_file  in
                                   FStar_All.pipe_right uu____58298
                                     FStar_Pervasives_Native.fst))
                            in
                         ((let uu____58322 = is_implementation file_name  in
                           if uu____58322
                           then
                             ((let uu____58326 =
                                 (FStar_Options.cmi ()) && widened  in
                               if uu____58326
                               then
                                 ((let uu____58330 = output_ml_file file_name
                                      in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____58330 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files));
                                  (let uu____58334 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____58334 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)))
                               else
                                 ((let uu____58341 = output_ml_file file_name
                                      in
                                   FStar_Util.print2 "%s: %s \n\n"
                                     uu____58341 cache_file_name1);
                                  (let uu____58344 =
                                     output_krml_file file_name  in
                                   FStar_Util.print2 "%s: %s\n\n" uu____58344
                                     cache_file_name1)));
                              (let cmx_files =
                                 let extracted_fst_files =
                                   FStar_All.pipe_right all_fst_files_dep
                                     (FStar_List.filter
                                        (fun df  ->
                                           (let uu____58369 =
                                              lowercase_module_name df  in
                                            let uu____58371 =
                                              lowercase_module_name file_name
                                               in
                                            uu____58369 <> uu____58371) &&
                                             (let uu____58375 =
                                                lowercase_module_name df  in
                                              FStar_Options.should_extract
                                                uu____58375)))
                                    in
                                 FStar_All.pipe_right extracted_fst_files
                                   (FStar_List.map output_cmx_file)
                                  in
                               let uu____58385 =
                                 let uu____58387 =
                                   lowercase_module_name file_name  in
                                 FStar_Options.should_extract uu____58387  in
                               if uu____58385
                               then
                                 let uu____58390 = output_cmx_file file_name
                                    in
                                 let uu____58392 = output_ml_file file_name
                                    in
                                 FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                   uu____58390 uu____58392
                                   (FStar_String.concat "\\\n\t" cmx_files)
                               else ()))
                           else
                             (let uu____58400 =
                                (let uu____58404 =
                                   let uu____58406 =
                                     lowercase_module_name file_name  in
                                   has_implementation deps.file_system_map
                                     uu____58406
                                    in
                                 Prims.op_Negation uu____58404) &&
                                  (is_interface file_name)
                                 in
                              if uu____58400
                              then
                                let uu____58409 =
                                  (FStar_Options.cmi ()) && widened  in
                                (if uu____58409
                                 then
                                   let uu____58412 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____58412 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)
                                 else
                                   (let uu____58418 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____58418 cache_file_name1))
                              else ()));
                          set_of_unchecked_files1)))) uu____58011
         in
      FStar_All.pipe_right keys uu____58000  in
    let uu____58429 =
      let uu____58440 =
        let uu____58444 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____58444
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____58440
        (fun l  ->
           let uu____58481 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____58481))
       in
    match uu____58429 with
    | (all_fst_files,all_unchecked_fst_files) ->
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____58539 = FStar_Options.should_extract mname  in
                  if uu____58539
                  then
                    let uu____58542 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____58542
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____58569 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____58569));
          sort_output_files krml_file_map  in
        ((let uu____58573 =
            let uu____58575 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58575 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____58573);
         (let uu____58594 =
            let uu____58596 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58596 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n"
            uu____58594);
         (let uu____58615 =
            let uu____58617 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58617 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____58615);
         (let uu____58635 =
            let uu____58637 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____58637 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____58635))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____58661 = FStar_Options.dep ()  in
    match uu____58661 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____58673 ->
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
         fun uu____58728  ->
           fun s  ->
             match uu____58728 with
             | (v0,v1) ->
                 let uu____58757 =
                   let uu____58759 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____58759  in
                 FStar_String.op_Hat s uu____58757) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____58780 =
        let uu____58782 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____58782  in
      has_interface deps.file_system_map uu____58780
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____58798 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____58798  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____58809 =
                   let uu____58811 = module_name_of_file f  in
                   FStar_String.lowercase uu____58811  in
                 uu____58809 = m)))
  