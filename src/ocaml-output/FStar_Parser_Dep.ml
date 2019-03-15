open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____45911 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____45922 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____45933 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | White  -> true | uu____45956 -> false
  
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Gray  -> true | uu____45967 -> false
  
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____45978 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____45989 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____46000 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____46048 =
             (l > lext) &&
               (let uu____46051 = FStar_String.substring f (l - lext) lext
                   in
                uu____46051 = ext)
              in
           if uu____46048
           then
             let uu____46058 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____46058
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____46065 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____46065 with
    | (FStar_Pervasives_Native.Some m)::uu____46079 ->
        FStar_Pervasives_Native.Some m
    | uu____46091 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46108 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____46108 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____46122 = is_interface f  in Prims.op_Negation uu____46122
  
let list_of_option :
  'Auu____46129 .
    'Auu____46129 FStar_Pervasives_Native.option -> 'Auu____46129 Prims.list
  =
  fun uu___423_46138  ->
    match uu___423_46138 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____46147 .
    ('Auu____46147 FStar_Pervasives_Native.option * 'Auu____46147
      FStar_Pervasives_Native.option) -> 'Auu____46147 Prims.list
  =
  fun uu____46162  ->
    match uu____46162 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46190 =
      let uu____46194 = FStar_Util.basename f  in
      check_and_strip_suffix uu____46194  in
    match uu____46190 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____46201 =
          let uu____46207 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____46207)  in
        FStar_Errors.raise_err uu____46201
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____46221 = module_name_of_file f  in
    FStar_String.lowercase uu____46221
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____46234 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____46234 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____46237 ->
        let uu____46240 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____46240
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____46280 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____46303 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UseImplementation _0 -> true
    | uu____46326 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____46349 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___424_46367  ->
    match uu___424_46367 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____46386 . unit -> 'Auu____46386 Prims.list =
  fun uu____46389  -> [] 
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
  fun uu____46731  ->
    fun k  -> match uu____46731 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____46753  ->
    fun k  ->
      fun v1  ->
        match uu____46753 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____46768  ->
    match uu____46768 with | Deps m -> FStar_Util.smap_keys m
  
let (deps_empty : unit -> dependence_graph) =
  fun uu____46780  ->
    let uu____46781 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____46781
  
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
  let uu____46839 = deps_empty ()  in
  let uu____46840 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____46852 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____46839 uu____46840 [] [] [] uu____46852 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___425_46865  ->
    match uu___425_46865 with
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
      let uu____46894 = FStar_Util.smap_try_find file_system_map key  in
      match uu____46894 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____46921) ->
          let uu____46943 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____46943
      | FStar_Pervasives_Native.Some
          (uu____46946,FStar_Pervasives_Native.Some fn) ->
          let uu____46969 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____46969
      | uu____46972 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47005 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47005 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____47032) ->
          FStar_Pervasives_Native.Some iface
      | uu____47055 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47088 = FStar_Util.smap_try_find file_system_map key  in
      match uu____47088 with
      | FStar_Pervasives_Native.Some
          (uu____47114,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____47138 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____47167 = interface_of file_system_map key  in
      FStar_Option.isSome uu____47167
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____47187 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____47187
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  fun fn  ->
    let cache_fn =
      let uu____47214 =
        let uu____47216 = FStar_Options.lax ()  in
        if uu____47216 then ".checked.lax" else ".checked"  in
      FStar_String.op_Hat fn uu____47214  in
    let uu____47224 =
      let uu____47228 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____47228  in
    match uu____47224 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____47249 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____47249
        then
          let uu____47260 =
            let uu____47266 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____47266)
             in
          FStar_Errors.raise_err uu____47260
        else
          (let uu____47278 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____47278, false))
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____47292 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____47292 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____47328 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____47328 FStar_Util.must
  
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
                      (let uu____47382 = lowercase_module_name fn  in
                       key = uu____47382)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____47401 = interface_of file_system_map key  in
              (match uu____47401 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47408 =
                     let uu____47414 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____47414)  in
                   FStar_Errors.raise_err uu____47408
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____47424 =
                (cmd_line_has_impl key) &&
                  (let uu____47427 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____47427)
                 in
              if uu____47424
              then
                let uu____47434 = FStar_Options.expose_interfaces ()  in
                (if uu____47434
                 then
                   let uu____47438 =
                     let uu____47440 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____47440  in
                   maybe_use_cache_of uu____47438
                 else
                   (let uu____47447 =
                      let uu____47453 =
                        let uu____47455 =
                          let uu____47457 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____47457  in
                        let uu____47462 =
                          let uu____47464 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____47464  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____47455 uu____47462
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____47453)
                       in
                    FStar_Errors.raise_err uu____47447))
              else
                (let uu____47474 =
                   let uu____47476 = interface_of file_system_map key  in
                   FStar_Option.get uu____47476  in
                 maybe_use_cache_of uu____47474)
          | PreferInterface key ->
              let uu____47483 = implementation_of file_system_map key  in
              (match uu____47483 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47489 =
                     let uu____47495 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47495)
                      in
                   FStar_Errors.raise_err uu____47489
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____47505 = implementation_of file_system_map key  in
              (match uu____47505 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47511 =
                     let uu____47517 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47517)
                      in
                   FStar_Errors.raise_err uu____47511
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____47527 = implementation_of file_system_map key  in
              (match uu____47527 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47533 =
                     let uu____47539 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47539)
                      in
                   FStar_Errors.raise_err uu____47533
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
          let uu____47600 = deps_try_find deps fn  in
          match uu____47600 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____47608;_} ->
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
    (let uu____47622 =
       let uu____47624 =
         let uu____47626 =
           let uu____47628 =
             let uu____47632 =
               let uu____47636 = deps_keys graph  in
               FStar_List.unique uu____47636  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____47650 =
                      let uu____47651 = deps_try_find graph k  in
                      FStar_Util.must uu____47651  in
                    uu____47650.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____47672 =
                      let uu____47674 = lowercase_module_name k  in
                      r uu____47674  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____47672
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____47632
              in
           FStar_String.concat "\n" uu____47628  in
         FStar_String.op_Hat uu____47626 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____47624  in
     FStar_Util.write_file "dep.graph" uu____47622)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____47695  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____47721 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____47721  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____47761 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____47761
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____47798 =
              let uu____47804 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____47804)  in
            FStar_Errors.raise_err uu____47798)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____47867 = FStar_Util.smap_try_find map1 key  in
      match uu____47867 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____47914 = is_interface full_path  in
          if uu____47914
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____47963 = is_interface full_path  in
          if uu____47963
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____48005 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____48023  ->
          match uu____48023 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____48005);
    FStar_List.iter
      (fun f  ->
         let uu____48042 = lowercase_module_name f  in
         add_entry uu____48042 f) filenames;
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
        (let uu____48074 =
           let uu____48078 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____48078  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____48114 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____48114  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____48074);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____48234 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____48234 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____48257 = string_of_lid l last1  in
      FStar_String.lowercase uu____48257
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____48266 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____48266
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____48288 =
        let uu____48290 =
          let uu____48292 =
            let uu____48294 =
              let uu____48298 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____48298  in
            FStar_Util.must uu____48294  in
          FStar_String.lowercase uu____48292  in
        uu____48290 <> k'  in
      if uu____48288
      then
        let uu____48303 = FStar_Ident.range_of_lid lid  in
        let uu____48304 =
          let uu____48310 =
            let uu____48312 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____48312 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____48310)  in
        FStar_Errors.log_issue uu____48303 uu____48304
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____48328 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____48350 = FStar_Options.prims_basename ()  in
      let uu____48352 =
        let uu____48356 = FStar_Options.pervasives_basename ()  in
        let uu____48358 =
          let uu____48362 = FStar_Options.pervasives_native_basename ()  in
          [uu____48362]  in
        uu____48356 :: uu____48358  in
      uu____48350 :: uu____48352  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____48405 =
         let uu____48408 = lowercase_module_name full_filename  in
         namespace_of_module uu____48408  in
       match uu____48405 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____48447 -> d = d'
  
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
        let uu____48487 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____48487
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____48522 =
             let uu____48523 = is_interface filename  in
             if uu____48523
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____48645 =
               let uu____48647 =
                 let uu____48649 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____48649  in
               Prims.op_Negation uu____48647  in
             if uu____48645
             then
               let uu____48676 =
                 let uu____48679 = FStar_ST.op_Bang deps1  in d ::
                   uu____48679
                  in
               FStar_ST.op_Colon_Equals deps1 uu____48676
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____48776 =
               resolve_module_name original_or_working_map key  in
             match uu____48776 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____48786 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____48786
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____48792 -> false  in
           let record_open_module let_open lid =
             let uu____48811 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____48811
             then true
             else
               (if let_open
                then
                  (let uu____48820 = FStar_Ident.range_of_lid lid  in
                   let uu____48821 =
                     let uu____48827 =
                       let uu____48829 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____48829
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____48827)
                      in
                   FStar_Errors.log_issue uu____48820 uu____48821)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____48849 = FStar_Ident.range_of_lid lid  in
               let uu____48850 =
                 let uu____48856 =
                   let uu____48858 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____48858
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____48856)
                  in
               FStar_Errors.log_issue uu____48849 uu____48850
             else ()  in
           let record_open let_open lid =
             let uu____48878 = record_open_module let_open lid  in
             if uu____48878
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____48895 =
             match uu____48895 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____48902 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____48919 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____48919  in
             let alias = lowercase_join_longident lid true  in
             let uu____48924 = FStar_Util.smap_try_find original_map alias
                in
             match uu____48924 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____48992 = FStar_Ident.range_of_lid lid  in
                   let uu____48993 =
                     let uu____48999 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____48999)
                      in
                   FStar_Errors.log_issue uu____48992 uu____48993);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____49010 = add_dependence_edge working_map module_name
                in
             if uu____49010
             then ()
             else
               (let uu____49015 = FStar_Options.debug_any ()  in
                if uu____49015
                then
                  let uu____49018 = FStar_Ident.range_of_lid module_name  in
                  let uu____49019 =
                    let uu____49025 =
                      let uu____49027 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____49027
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____49025)
                     in
                  FStar_Errors.log_issue uu____49018 uu____49019
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____49039 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_49167 =
              match uu___426_49167 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49178 =
                        let uu____49180 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49180
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____49186) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49197 =
                        let uu____49199 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49199
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
                  let uu____49221 =
                    let uu____49222 = lowercase_join_longident lid true  in
                    FriendImplementation uu____49222  in
                  add_dep deps uu____49221
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____49227 = record_module_alias ident lid  in
                  if uu____49227
                  then
                    let uu____49230 =
                      let uu____49231 = lowercase_join_longident lid true  in
                      dep_edge uu____49231  in
                    add_dep deps uu____49230
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____49236,patterms) ->
                  FStar_List.iter
                    (fun uu____49258  ->
                       match uu____49258 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____49267,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____49273,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49275;
                    FStar_Parser_AST.mdest = uu____49276;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49278;
                    FStar_Parser_AST.mdest = uu____49279;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____49281,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49283;
                    FStar_Parser_AST.mdest = uu____49284;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____49288,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____49327  ->
                           match uu____49327 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____49340,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____49347 -> ()
              | FStar_Parser_AST.Pragma uu____49348 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____49351 =
                      let uu____49353 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____49353 > (Prims.parse_int "1")  in
                    if uu____49351
                    then
                      let uu____49378 =
                        let uu____49384 =
                          let uu____49386 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____49386
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____49384)
                         in
                      let uu____49391 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____49378 uu____49391
                    else ()))
            
            and collect_tycon uu___427_49394 =
              match uu___427_49394 with
              | FStar_Parser_AST.TyconAbstract (uu____49395,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____49407,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____49421,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49467  ->
                        match uu____49467 with
                        | (uu____49476,t,uu____49478) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____49483,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49545  ->
                        match uu____49545 with
                        | (uu____49559,t,uu____49561,uu____49562) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_49573 =
              match uu___428_49573 with
              | FStar_Parser_AST.DefineEffect (uu____49574,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____49588,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____49601,t);
                   FStar_Parser_AST.brange = uu____49603;
                   FStar_Parser_AST.blevel = uu____49604;
                   FStar_Parser_AST.aqual = uu____49605;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____49608,t);
                   FStar_Parser_AST.brange = uu____49610;
                   FStar_Parser_AST.blevel = uu____49611;
                   FStar_Parser_AST.aqual = uu____49612;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____49616;
                   FStar_Parser_AST.blevel = uu____49617;
                   FStar_Parser_AST.aqual = uu____49618;_} -> collect_term t
               | uu____49621 -> ())
            
            and collect_aqual uu___429_49622 =
              match uu___429_49622 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____49626 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_49630 =
              match uu___430_49630 with
              | FStar_Const.Const_int
                  (uu____49631,FStar_Pervasives_Native.Some
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
                  let uu____49658 =
                    let uu____49659 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____49659  in
                  add_dep deps uu____49658
              | FStar_Const.Const_char uu____49662 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____49665 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____49667 -> ()
            
            and collect_term' uu___433_49668 =
              match uu___433_49668 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____49677 =
                      let uu____49679 = FStar_Ident.text_of_id s  in
                      uu____49679 = "@"  in
                    if uu____49677
                    then
                      let uu____49684 =
                        let uu____49685 =
                          let uu____49686 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____49686
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____49685  in
                      collect_term' uu____49684
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____49690 -> ()
              | FStar_Parser_AST.Uvar uu____49691 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____49694) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____49719  ->
                        match uu____49719 with
                        | (t,uu____49725) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____49735) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____49737,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____49787  ->
                        match uu____49787 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____49816 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____49826,t1,t2) ->
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
                     (fun uu____49922  ->
                        match uu____49922 with
                        | (uu____49927,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____49930) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_49959  ->
                        match uu___431_49959 with
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
              | FStar_Parser_AST.NamedTyp (uu____50007,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____50011) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____50019) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____50027,uu____50028) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____50034) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____50048 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____50048);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_50058  ->
                        match uu___432_50058 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_50068 =
              match uu___434_50068 with
              | FStar_Parser_AST.PatVar (uu____50069,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____50075,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____50084 -> ()
              | FStar_Parser_AST.PatConst uu____50085 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____50093 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____50101) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____50122  ->
                       match uu____50122 with
                       | (uu____50127,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____50172 =
              match uu____50172 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____50190 = FStar_Parser_Driver.parse_file filename  in
            match uu____50190 with
            | (ast,uu____50203) ->
                let mname = lowercase_module_name filename  in
                ((let uu____50221 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____50221
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____50227 = FStar_ST.op_Bang deps  in
                  let uu____50253 = FStar_ST.op_Bang mo_roots  in
                  let uu____50279 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____50227;
                    additional_roots = uu____50253;
                    has_inline_for_extraction = uu____50279
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____50318 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____50318 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____50440 = dep_graph  in
    match uu____50440 with
    | Deps g -> let uu____50444 = FStar_Util.smap_copy g  in Deps uu____50444
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____50589 filename =
              match uu____50589 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____50630 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____50630  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____50661 = FStar_Options.debug_any ()  in
                         if uu____50661
                         then
                           let uu____50664 =
                             let uu____50666 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____50666  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____50664
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1245_50677 = dep_node  in
                           { edges = (uu___1245_50677.edges); color = Gray });
                        (let uu____50678 =
                           let uu____50689 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____50689
                            in
                         match uu____50678 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1251_50725 = dep_node  in
                                 {
                                   edges = (uu___1251_50725.edges);
                                   color = Black
                                 });
                              (let uu____50727 = FStar_Options.debug_any ()
                                  in
                               if uu____50727
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____50733 =
                                 let uu____50737 =
                                   FStar_List.collect
                                     (fun uu___435_50744  ->
                                        match uu___435_50744 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____50737 all_friends1
                                  in
                               (uu____50733, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____50810 = FStar_Options.debug_any ()  in
             if uu____50810
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____50839 = deps  in
               match uu____50839 with
               | Deps dg ->
                   let uu____50843 = deps_empty ()  in
                   (match uu____50843 with
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
                                  | uu____50893 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____50901  ->
                                  let uu____50903 =
                                    let uu___1286_50904 = dep_node  in
                                    let uu____50905 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____50905; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____50903) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____50907 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____50907
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____50912 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____50912 with
             | (friends,all_files_0) ->
                 ((let uu____50955 = FStar_Options.debug_any ()  in
                   if uu____50955
                   then
                     let uu____50958 =
                       let uu____50960 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____50960  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____50958
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____50979 =
                     (let uu____50991 = FStar_Options.debug_any ()  in
                      if uu____50991
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____50979 with
                   | (uu____51014,all_files) ->
                       ((let uu____51029 = FStar_Options.debug_any ()  in
                         if uu____51029
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____51036 = FStar_ST.op_Bang widened  in
                         (all_files, uu____51036))))))
  
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
                let uu____51122 = FStar_Options.find_file fn  in
                match uu____51122 with
                | FStar_Pervasives_Native.None  ->
                    let uu____51128 =
                      let uu____51134 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____51134)
                       in
                    FStar_Errors.raise_err uu____51128
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____51164 =
          let uu____51168 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____51168  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____51164  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____51235 =
          let uu____51237 = deps_try_find dep_graph file_name  in
          uu____51237 = FStar_Pervasives_Native.None  in
        if uu____51235
        then
          let uu____51243 =
            let uu____51255 =
              let uu____51269 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____51269 file_name  in
            match uu____51255 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____51243 with
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
                  let uu____51413 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____51413
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____51421 = FStar_List.unique deps1  in
                  { edges = uu____51421; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____51423 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____51423)))
        else ()  in
      FStar_List.iter discover_one all_cmd_line_files1;
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____51463 =
            let uu____51469 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____51469)  in
          FStar_Errors.raise_err uu____51463)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____51506 = deps_try_find dep_graph1 filename  in
             match uu____51506 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____51510 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____51510
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____51524 =
                           implementation_of file_system_map f  in
                         (match uu____51524 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51535 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____51541 =
                           implementation_of file_system_map f  in
                         (match uu____51541 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51552 -> [x; UseImplementation f])
                     | uu____51556 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1370_51559 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____51561 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____51561);
                deps_add_dep dep_graph1 filename
                  (let uu___1375_51571 = node  in
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
        let uu____51615 =
          let uu____51624 =
            let uu____51626 = FStar_Options.codegen ()  in
            uu____51626 <> FStar_Pervasives_Native.None  in
          topological_dependences_of file_system_map dep_graph
            inlining_ifaces all_cmd_line_files1 uu____51624
           in
        match uu____51615 with
        | (all_files,uu____51639) ->
            ((let uu____51649 = FStar_Options.debug_any ()  in
              if uu____51649
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
          let uu____51719 = FStar_Options.find_file fn  in
          match uu____51719 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____51727 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____51741 = FStar_Options.debug_any ()  in
           if uu____51741
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____51760 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____51760
          then
            let uu____51771 =
              let uu____51778 =
                let uu____51780 =
                  let uu____51782 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____51782  in
                digest_of_file1 uu____51780  in
              ("interface", uu____51778)  in
            [uu____51771]
          else []  in
        let binary_deps =
          let uu____51814 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____51814
            (FStar_List.filter
               (fun fn2  ->
                  let uu____51829 =
                    (is_interface fn2) &&
                      (let uu____51832 = lowercase_module_name fn2  in
                       uu____51832 = module_name)
                     in
                  Prims.op_Negation uu____51829))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____51848 = lowercase_module_name fn11  in
                 let uu____51850 = lowercase_module_name fn2  in
                 FStar_String.compare uu____51848 uu____51850) binary_deps
           in
        let rec hash_deps out uu___436_51886 =
          match uu___436_51886 with
          | [] ->
              FStar_Util.Inr
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____51953 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____51953
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____51974 = FStar_Options.debug_any ()  in
                     if uu____51974
                     then
                       let uu____51977 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____51977
                     else ());
                    (let uu____51982 =
                       FStar_Util.format1 "cache file %s does not exist"
                         cache_fn
                        in
                     FStar_Util.Inl uu____51982))
               | FStar_Pervasives_Native.Some dig ->
                   let uu____51997 =
                     let uu____52006 =
                       let uu____52013 = lowercase_module_name fn2  in
                       (uu____52013, dig)  in
                     uu____52006 :: out  in
                   hash_deps uu____51997 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____52053 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____52079  ->
              match uu____52079 with
              | (m,d) ->
                  let uu____52093 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____52093))
       in
    FStar_All.pipe_right uu____52053 (FStar_String.concat "\n")
  
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
              let uu____52128 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____52128 FStar_Option.get  in
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
    let uu____52157 = deps.dep_graph  in
    match uu____52157 with
    | Deps deps1 ->
        let uu____52161 =
          let uu____52163 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____52181 =
                       let uu____52183 =
                         let uu____52185 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____52185
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____52183
                        in
                     uu____52181 :: out) []
             in
          FStar_All.pipe_right uu____52163 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____52161 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____52257 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____52257) ||
          (let uu____52264 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____52264)
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
            let uu____52307 =
              let uu____52311 = FStar_ST.op_Bang order  in ml_file ::
                uu____52311
               in
            FStar_ST.op_Colon_Equals order uu____52307
         in
      let rec aux uu___437_52374 =
        match uu___437_52374 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____52402 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____52402 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____52405 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____52405
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____52409;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____52418 = should_visit lc_module_name  in
              if uu____52418
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____52426 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____52426);
                 (let uu____52431 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____52431);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____52443 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____52443)
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____52495 =
          let uu____52497 =
            let uu____52501 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____52501  in
          FStar_Option.get uu____52497  in
        FStar_Util.replace_chars uu____52495 46 "_"  in
      let uu____52506 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____52506  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____52528 = output_file ".ml" f  in norm_path uu____52528  in
    let output_krml_file f =
      let uu____52540 = output_file ".krml" f  in norm_path uu____52540  in
    let output_cmx_file f =
      let uu____52552 = output_file ".cmx" f  in norm_path uu____52552  in
    let cache_file f =
      let uu____52569 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____52569
        (fun uu____52598  ->
           match uu____52598 with | (f1,b) -> ((norm_path f1), b))
       in
    let set_of_unchecked_files =
      let uu____52623 =
        let uu____52634 = FStar_Util.new_set FStar_Util.compare  in
        FStar_List.fold_left
          (fun set_of_unchecked_files  ->
             fun file_name  ->
               let dep_node =
                 let uu____52671 = deps_try_find deps.dep_graph file_name  in
                 FStar_All.pipe_right uu____52671 FStar_Option.get  in
               let iface_deps =
                 let uu____52681 = is_interface file_name  in
                 if uu____52681
                 then FStar_Pervasives_Native.None
                 else
                   (let uu____52692 =
                      let uu____52696 = lowercase_module_name file_name  in
                      interface_of deps.file_system_map uu____52696  in
                    match uu____52692 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some iface ->
                        let uu____52708 =
                          let uu____52711 =
                            let uu____52712 =
                              deps_try_find deps.dep_graph iface  in
                            FStar_Option.get uu____52712  in
                          uu____52711.edges  in
                        FStar_Pervasives_Native.Some uu____52708)
                  in
               let iface_deps1 =
                 FStar_Util.map_opt iface_deps
                   (FStar_List.filter
                      (fun iface_dep  ->
                         let uu____52729 =
                           FStar_Util.for_some (dep_subsumed_by iface_dep)
                             dep_node.edges
                            in
                         Prims.op_Negation uu____52729))
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
               let uu____52788 = cache_file file_name  in
               match uu____52788 with
               | (cache_file_name1,b) ->
                   let set_of_unchecked_files1 =
                     if b
                     then set_of_unchecked_files
                     else FStar_Util.set_add file_name set_of_unchecked_files
                      in
                   (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1
                      norm_f files4;
                    (let uu____52817 =
                       let uu____52826 = FStar_Options.cmi ()  in
                       if uu____52826
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
                          let uu____52874 =
                            FStar_Util.remove_dups
                              (fun x  -> fun y  -> x = y)
                              (FStar_List.append fst_files
                                 fst_files_from_iface)
                             in
                          (uu____52874, false))
                        in
                     match uu____52817 with
                     | (all_fst_files_dep,widened) ->
                         let all_checked_fst_dep_files =
                           FStar_All.pipe_right all_fst_files_dep
                             (FStar_List.map
                                (fun f  ->
                                   let uu____52921 =
                                     FStar_All.pipe_right f cache_file  in
                                   FStar_All.pipe_right uu____52921
                                     FStar_Pervasives_Native.fst))
                            in
                         ((let uu____52945 = is_implementation file_name  in
                           if uu____52945
                           then
                             ((let uu____52949 =
                                 (FStar_Options.cmi ()) && widened  in
                               if uu____52949
                               then
                                 ((let uu____52953 = output_ml_file file_name
                                      in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____52953 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files));
                                  (let uu____52957 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____52957 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)))
                               else
                                 ((let uu____52964 = output_ml_file file_name
                                      in
                                   FStar_Util.print2 "%s: %s \n\n"
                                     uu____52964 cache_file_name1);
                                  (let uu____52967 =
                                     output_krml_file file_name  in
                                   FStar_Util.print2 "%s: %s\n\n" uu____52967
                                     cache_file_name1)));
                              (let cmx_files =
                                 let extracted_fst_files =
                                   FStar_All.pipe_right all_fst_files_dep
                                     (FStar_List.filter
                                        (fun df  ->
                                           (let uu____52992 =
                                              lowercase_module_name df  in
                                            let uu____52994 =
                                              lowercase_module_name file_name
                                               in
                                            uu____52992 <> uu____52994) &&
                                             (let uu____52998 =
                                                lowercase_module_name df  in
                                              FStar_Options.should_extract
                                                uu____52998)))
                                    in
                                 FStar_All.pipe_right extracted_fst_files
                                   (FStar_List.map output_cmx_file)
                                  in
                               let uu____53008 =
                                 let uu____53010 =
                                   lowercase_module_name file_name  in
                                 FStar_Options.should_extract uu____53010  in
                               if uu____53008
                               then
                                 let uu____53013 = output_cmx_file file_name
                                    in
                                 let uu____53015 = output_ml_file file_name
                                    in
                                 FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                   uu____53013 uu____53015
                                   (FStar_String.concat "\\\n\t" cmx_files)
                               else ()))
                           else
                             (let uu____53023 =
                                (let uu____53027 =
                                   let uu____53029 =
                                     lowercase_module_name file_name  in
                                   has_implementation deps.file_system_map
                                     uu____53029
                                    in
                                 Prims.op_Negation uu____53027) &&
                                  (is_interface file_name)
                                 in
                              if uu____53023
                              then
                                let uu____53032 =
                                  (FStar_Options.cmi ()) && widened  in
                                (if uu____53032
                                 then
                                   let uu____53035 =
                                     output_krml_file file_name  in
                                   FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                     uu____53035 cache_file_name1
                                     (FStar_String.concat " \\\n\t"
                                        all_checked_fst_dep_files)
                                 else
                                   (let uu____53041 =
                                      output_krml_file file_name  in
                                    FStar_Util.print2 "%s: %s \n\n"
                                      uu____53041 cache_file_name1))
                              else ()));
                          set_of_unchecked_files1)))) uu____52634
         in
      FStar_All.pipe_right keys uu____52623  in
    let uu____53052 =
      let uu____53063 =
        let uu____53067 =
          FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
        FStar_All.pipe_right uu____53067
          (FStar_Util.sort_with FStar_String.compare)
         in
      FStar_All.pipe_right uu____53063
        (fun l  ->
           let uu____53104 =
             FStar_All.pipe_right l
               (FStar_List.filter
                  (fun f  -> FStar_Util.set_mem f set_of_unchecked_files))
              in
           (l, uu____53104))
       in
    match uu____53052 with
    | (all_fst_files,all_unchecked_fst_files) ->
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
          let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
             in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____53192 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____53192));
          sort_output_files krml_file_map  in
        ((let uu____53196 =
            let uu____53198 =
              FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53198 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____53196);
         (let uu____53217 =
            let uu____53219 =
              FStar_All.pipe_right all_unchecked_fst_files
                (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53219 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n"
            uu____53217);
         (let uu____53238 =
            let uu____53240 =
              FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53240 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____53238);
         (let uu____53258 =
            let uu____53260 =
              FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
               in
            FStar_All.pipe_right uu____53260 (FStar_String.concat " \\\n\t")
             in
          FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____53258))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____53284 = FStar_Options.dep ()  in
    match uu____53284 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____53296 ->
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
         fun uu____53351  ->
           fun s  ->
             match uu____53351 with
             | (v0,v1) ->
                 let uu____53380 =
                   let uu____53382 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____53382  in
                 FStar_String.op_Hat s uu____53380) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____53403 =
        let uu____53405 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53405  in
      has_interface deps.file_system_map uu____53403
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____53421 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53421  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____53432 =
                   let uu____53434 = module_name_of_file f  in
                   FStar_String.lowercase uu____53434  in
                 uu____53432 = m)))
  