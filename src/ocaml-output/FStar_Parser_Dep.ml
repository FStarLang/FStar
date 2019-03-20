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
  
let (cache_file_name_internal : Prims.string -> (Prims.string * Prims.bool))
  =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let uu____47272 =
      let uu____47276 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____47276  in
    match uu____47272 with
    | FStar_Pervasives_Native.Some path -> (path, true)
    | FStar_Pervasives_Native.None  ->
        let mname = FStar_All.pipe_right fn module_name_of_file  in
        let uu____47297 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____47297
        then
          let uu____47308 =
            let uu____47314 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____47314)
             in
          FStar_Errors.raise_err uu____47308
        else
          (let uu____47326 = FStar_Options.prepend_cache_dir cache_fn  in
           (uu____47326, false))
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____47385 = FStar_Util.smap_try_find memo x  in
    match uu____47385 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____47448 = FStar_All.pipe_right fn cache_file_name_internal  in
    FStar_All.pipe_right uu____47448 FStar_Pervasives_Native.fst
  
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____47484 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____47484 FStar_Util.must
  
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
                      (let uu____47538 = lowercase_module_name fn  in
                       key = uu____47538)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____47557 = interface_of file_system_map key  in
              (match uu____47557 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47564 =
                     let uu____47570 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____47570)  in
                   FStar_Errors.raise_err uu____47564
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____47580 =
                (cmd_line_has_impl key) &&
                  (let uu____47583 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____47583)
                 in
              if uu____47580
              then
                let uu____47590 = FStar_Options.expose_interfaces ()  in
                (if uu____47590
                 then
                   let uu____47594 =
                     let uu____47596 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____47596  in
                   maybe_use_cache_of uu____47594
                 else
                   (let uu____47603 =
                      let uu____47609 =
                        let uu____47611 =
                          let uu____47613 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____47613  in
                        let uu____47618 =
                          let uu____47620 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____47620  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____47611 uu____47618
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____47609)
                       in
                    FStar_Errors.raise_err uu____47603))
              else
                (let uu____47630 =
                   let uu____47632 = interface_of file_system_map key  in
                   FStar_Option.get uu____47632  in
                 maybe_use_cache_of uu____47630)
          | PreferInterface key ->
              let uu____47639 = implementation_of file_system_map key  in
              (match uu____47639 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47645 =
                     let uu____47651 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47651)
                      in
                   FStar_Errors.raise_err uu____47645
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____47661 = implementation_of file_system_map key  in
              (match uu____47661 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47667 =
                     let uu____47673 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47673)
                      in
                   FStar_Errors.raise_err uu____47667
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____47683 = implementation_of file_system_map key  in
              (match uu____47683 with
               | FStar_Pervasives_Native.None  ->
                   let uu____47689 =
                     let uu____47695 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____47695)
                      in
                   FStar_Errors.raise_err uu____47689
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
          let uu____47756 = deps_try_find deps fn  in
          match uu____47756 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____47764;_} ->
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
    (let uu____47778 =
       let uu____47780 =
         let uu____47782 =
           let uu____47784 =
             let uu____47788 =
               let uu____47792 = deps_keys graph  in
               FStar_List.unique uu____47792  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____47806 =
                      let uu____47807 = deps_try_find graph k  in
                      FStar_Util.must uu____47807  in
                    uu____47806.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____47828 =
                      let uu____47830 = lowercase_module_name k  in
                      r uu____47830  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____47828
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____47788
              in
           FStar_String.concat "\n" uu____47784  in
         FStar_String.op_Hat uu____47782 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____47780  in
     FStar_Util.write_file "dep.graph" uu____47778)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____47851  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____47877 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____47877  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____47917 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____47917
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____47954 =
              let uu____47960 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____47960)  in
            FStar_Errors.raise_err uu____47954)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____48023 = FStar_Util.smap_try_find map1 key  in
      match uu____48023 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____48070 = is_interface full_path  in
          if uu____48070
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____48119 = is_interface full_path  in
          if uu____48119
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____48161 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____48179  ->
          match uu____48179 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____48161);
    FStar_List.iter
      (fun f  ->
         let uu____48198 = lowercase_module_name f  in
         add_entry uu____48198 f) filenames;
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
        (let uu____48230 =
           let uu____48234 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____48234  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____48270 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____48270  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____48230);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____48390 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____48390 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____48413 = string_of_lid l last1  in
      FStar_String.lowercase uu____48413
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____48422 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____48422
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____48444 =
        let uu____48446 =
          let uu____48448 =
            let uu____48450 =
              let uu____48454 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____48454  in
            FStar_Util.must uu____48450  in
          FStar_String.lowercase uu____48448  in
        uu____48446 <> k'  in
      if uu____48444
      then
        let uu____48459 = FStar_Ident.range_of_lid lid  in
        let uu____48460 =
          let uu____48466 =
            let uu____48468 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____48468 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____48466)  in
        FStar_Errors.log_issue uu____48459 uu____48460
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____48484 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____48506 = FStar_Options.prims_basename ()  in
      let uu____48508 =
        let uu____48512 = FStar_Options.pervasives_basename ()  in
        let uu____48514 =
          let uu____48518 = FStar_Options.pervasives_native_basename ()  in
          [uu____48518]  in
        uu____48512 :: uu____48514  in
      uu____48506 :: uu____48508  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____48561 =
         let uu____48564 = lowercase_module_name full_filename  in
         namespace_of_module uu____48564  in
       match uu____48561 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____48603 -> d = d'
  
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
        let uu____48643 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____48643
        then FStar_All.pipe_right data_from_cache FStar_Util.must
        else
          (let deps = FStar_Util.mk_ref []  in
           let mo_roots = FStar_Util.mk_ref []  in
           let has_inline_for_extraction = FStar_Util.mk_ref false  in
           let set_interface_inlining uu____48678 =
             let uu____48679 = is_interface filename  in
             if uu____48679
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ()  in
           let add_dep deps1 d =
             let uu____48801 =
               let uu____48803 =
                 let uu____48805 = FStar_ST.op_Bang deps1  in
                 FStar_List.existsML (dep_subsumed_by d) uu____48805  in
               Prims.op_Negation uu____48803  in
             if uu____48801
             then
               let uu____48832 =
                 let uu____48835 = FStar_ST.op_Bang deps1  in d ::
                   uu____48835
                  in
               FStar_ST.op_Colon_Equals deps1 uu____48832
             else ()  in
           let working_map = FStar_Util.smap_copy original_map  in
           let dep_edge module_name = PreferInterface module_name  in
           let add_dependence_edge original_or_working_map lid =
             let key = lowercase_join_longident lid true  in
             let uu____48932 =
               resolve_module_name original_or_working_map key  in
             match uu____48932 with
             | FStar_Pervasives_Native.Some module_name ->
                 (add_dep deps (dep_edge module_name);
                  (let uu____48942 =
                     (has_interface original_or_working_map module_name) &&
                       (has_implementation original_or_working_map
                          module_name)
                      in
                   if uu____48942
                   then add_dep mo_roots (UseImplementation module_name)
                   else ());
                  true)
             | uu____48948 -> false  in
           let record_open_module let_open lid =
             let uu____48967 =
               (let_open && (add_dependence_edge working_map lid)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid))
                in
             if uu____48967
             then true
             else
               (if let_open
                then
                  (let uu____48976 = FStar_Ident.range_of_lid lid  in
                   let uu____48977 =
                     let uu____48983 =
                       let uu____48985 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____48985
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____48983)
                      in
                   FStar_Errors.log_issue uu____48976 uu____48977)
                else ();
                false)
              in
           let record_open_namespace lid =
             let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____49005 = FStar_Ident.range_of_lid lid  in
               let uu____49006 =
                 let uu____49012 =
                   let uu____49014 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____49014
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____49012)
                  in
               FStar_Errors.log_issue uu____49005 uu____49006
             else ()  in
           let record_open let_open lid =
             let uu____49034 = record_open_module let_open lid  in
             if uu____49034
             then ()
             else
               if Prims.op_Negation let_open
               then record_open_namespace lid
               else ()
              in
           let record_open_module_or_namespace uu____49051 =
             match uu____49051 with
             | (lid,kind) ->
                 (match kind with
                  | Open_namespace  -> record_open_namespace lid
                  | Open_module  ->
                      let uu____49058 = record_open_module false lid  in ())
              in
           let record_module_alias ident lid =
             let key =
               let uu____49075 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____49075  in
             let alias = lowercase_join_longident lid true  in
             let uu____49080 = FStar_Util.smap_try_find original_map alias
                in
             match uu____49080 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____49148 = FStar_Ident.range_of_lid lid  in
                   let uu____49149 =
                     let uu____49155 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____49155)
                      in
                   FStar_Errors.log_issue uu____49148 uu____49149);
                  false)
              in
           let add_dep_on_module module_name =
             let uu____49166 = add_dependence_edge working_map module_name
                in
             if uu____49166
             then ()
             else
               (let uu____49171 = FStar_Options.debug_any ()  in
                if uu____49171
                then
                  let uu____49174 = FStar_Ident.range_of_lid module_name  in
                  let uu____49175 =
                    let uu____49181 =
                      let uu____49183 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____49183
                       in
                    (FStar_Errors.Warning_UnboundModuleReference,
                      uu____49181)
                     in
                  FStar_Errors.log_issue uu____49174 uu____49175
                else ())
              in
           let record_lid lid =
             match lid.FStar_Ident.ns with
             | [] -> ()
             | uu____49195 ->
                 let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                    in
                 add_dep_on_module module_name
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record_open_module_or_namespace auto_open;
           (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
               in
            let rec collect_module uu___426_49323 =
              match uu___426_49323 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49334 =
                        let uu____49336 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49336
                         in
                      ())
                   else ();
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____49342) ->
                  (check_module_declaration_against_filename lid filename;
                   if
                     (FStar_List.length lid.FStar_Ident.ns) >
                       (Prims.parse_int "0")
                   then
                     (let uu____49353 =
                        let uu____49355 = namespace_of_lid lid  in
                        enter_namespace original_map working_map uu____49355
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
                  let uu____49377 =
                    let uu____49378 = lowercase_join_longident lid true  in
                    FriendImplementation uu____49378  in
                  add_dep deps uu____49377
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____49383 = record_module_alias ident lid  in
                  if uu____49383
                  then
                    let uu____49386 =
                      let uu____49387 = lowercase_join_longident lid true  in
                      dep_edge uu____49387  in
                    add_dep deps uu____49386
                  else ()
              | FStar_Parser_AST.TopLevelLet (uu____49392,patterms) ->
                  FStar_List.iter
                    (fun uu____49414  ->
                       match uu____49414 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____49423,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____49429,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49431;
                    FStar_Parser_AST.mdest = uu____49432;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49434;
                    FStar_Parser_AST.mdest = uu____49435;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____49437,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____49439;
                    FStar_Parser_AST.mdest = uu____49440;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____49444,tc,ts) ->
                  (if tc
                   then record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____49483  ->
                           match uu____49483 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____49496,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____49503 -> ()
              | FStar_Parser_AST.Pragma uu____49504 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____49507 =
                      let uu____49509 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____49509 > (Prims.parse_int "1")  in
                    if uu____49507
                    then
                      let uu____49534 =
                        let uu____49540 =
                          let uu____49542 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____49542
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____49540)
                         in
                      let uu____49547 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____49534 uu____49547
                    else ()))
            
            and collect_tycon uu___427_49550 =
              match uu___427_49550 with
              | FStar_Parser_AST.TyconAbstract (uu____49551,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____49563,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____49577,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49623  ->
                        match uu____49623 with
                        | (uu____49632,t,uu____49634) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____49639,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____49701  ->
                        match uu____49701 with
                        | (uu____49715,t,uu____49717,uu____49718) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___428_49729 =
              match uu___428_49729 with
              | FStar_Parser_AST.DefineEffect (uu____49730,binders,t,decls)
                  ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____49744,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____49757,t);
                   FStar_Parser_AST.brange = uu____49759;
                   FStar_Parser_AST.blevel = uu____49760;
                   FStar_Parser_AST.aqual = uu____49761;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____49764,t);
                   FStar_Parser_AST.brange = uu____49766;
                   FStar_Parser_AST.blevel = uu____49767;
                   FStar_Parser_AST.aqual = uu____49768;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____49772;
                   FStar_Parser_AST.blevel = uu____49773;
                   FStar_Parser_AST.aqual = uu____49774;_} -> collect_term t
               | uu____49777 -> ())
            
            and collect_aqual uu___429_49778 =
              match uu___429_49778 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____49782 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___430_49786 =
              match uu___430_49786 with
              | FStar_Const.Const_int
                  (uu____49787,FStar_Pervasives_Native.Some
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
                  let uu____49814 =
                    let uu____49815 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    dep_edge uu____49815  in
                  add_dep deps uu____49814
              | FStar_Const.Const_char uu____49818 ->
                  add_dep deps (dep_edge "fstar.char")
              | FStar_Const.Const_float uu____49821 ->
                  add_dep deps (dep_edge "fstar.float")
              | uu____49823 -> ()
            
            and collect_term' uu___433_49824 =
              match uu___433_49824 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____49833 =
                      let uu____49835 = FStar_Ident.text_of_id s  in
                      uu____49835 = "@"  in
                    if uu____49833
                    then
                      let uu____49840 =
                        let uu____49841 =
                          let uu____49842 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____49842
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____49841  in
                      collect_term' uu____49840
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____49846 -> ()
              | FStar_Parser_AST.Uvar uu____49847 -> ()
              | FStar_Parser_AST.Var lid -> record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____49850) ->
                  record_lid lid
              | FStar_Parser_AST.Discrim lid -> record_lid lid
              | FStar_Parser_AST.Name lid -> record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record_lid lid;
                   FStar_List.iter
                     (fun uu____49875  ->
                        match uu____49875 with
                        | (t,uu____49881) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____49891) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____49893,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____49943  ->
                        match uu____49943 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____49972 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____49982,t1,t2) ->
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
                     (fun uu____50078  ->
                        match uu____50078 with
                        | (uu____50083,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____50086) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___431_50115  ->
                        match uu___431_50115 with
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
              | FStar_Parser_AST.NamedTyp (uu____50163,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____50167) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____50175) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____50183,uu____50184) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____50190) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____50204 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    add_dep_on_module uu____50204);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___432_50214  ->
                        match uu___432_50214 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___434_50224 =
              match uu___434_50224 with
              | FStar_Parser_AST.PatVar (uu____50225,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____50231,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____50240 -> ()
              | FStar_Parser_AST.PatConst uu____50241 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____50249 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____50257) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____50278  ->
                       match uu____50278 with
                       | (uu____50283,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____50328 =
              match uu____50328 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____50346 = FStar_Parser_Driver.parse_file filename  in
            match uu____50346 with
            | (ast,uu____50359) ->
                let mname = lowercase_module_name filename  in
                ((let uu____50377 =
                    (is_interface filename) &&
                      (has_implementation original_map mname)
                     in
                  if uu____50377
                  then add_dep mo_roots (UseImplementation mname)
                  else ());
                 collect_module ast;
                 (let uu____50383 = FStar_ST.op_Bang deps  in
                  let uu____50409 = FStar_ST.op_Bang mo_roots  in
                  let uu____50435 =
                    FStar_ST.op_Bang has_inline_for_extraction  in
                  {
                    direct_deps = uu____50383;
                    additional_roots = uu____50409;
                    has_inline_for_extraction = uu____50435
                  }))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____50474 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____50474 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____50596 = dep_graph  in
    match uu____50596 with
    | Deps g -> let uu____50600 = FStar_Util.smap_copy g  in Deps uu____50600
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____50745 filename =
              match uu____50745 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____50786 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____50786  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____50817 = FStar_Options.debug_any ()  in
                         if uu____50817
                         then
                           let uu____50820 =
                             let uu____50822 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____50822  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____50820
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1256_50833 = dep_node  in
                           { edges = (uu___1256_50833.edges); color = Gray });
                        (let uu____50834 =
                           let uu____50845 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____50845
                            in
                         match uu____50834 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1262_50881 = dep_node  in
                                 {
                                   edges = (uu___1262_50881.edges);
                                   color = Black
                                 });
                              (let uu____50883 = FStar_Options.debug_any ()
                                  in
                               if uu____50883
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____50889 =
                                 let uu____50893 =
                                   FStar_List.collect
                                     (fun uu___435_50900  ->
                                        match uu___435_50900 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____50893 all_friends1
                                  in
                               (uu____50889, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____50966 = FStar_Options.debug_any ()  in
             if uu____50966
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____50995 = deps  in
               match uu____50995 with
               | Deps dg ->
                   let uu____50999 = deps_empty ()  in
                   (match uu____50999 with
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
                                  | uu____51049 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____51057  ->
                                  let uu____51059 =
                                    let uu___1297_51060 = dep_node  in
                                    let uu____51061 =
                                      widen_one dep_node.edges  in
                                    { edges = uu____51061; color = White }
                                     in
                                  FStar_Util.smap_add dg' filename
                                    uu____51059) ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____51063 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____51063
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____51068 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____51068 with
             | (friends,all_files_0) ->
                 ((let uu____51111 = FStar_Options.debug_any ()  in
                   if uu____51111
                   then
                     let uu____51114 =
                       let uu____51116 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____51116  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____51114
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____51135 =
                     (let uu____51147 = FStar_Options.debug_any ()  in
                      if uu____51147
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____51135 with
                   | (uu____51170,all_files) ->
                       ((let uu____51185 = FStar_Options.debug_any ()  in
                         if uu____51185
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____51192 = FStar_ST.op_Bang widened  in
                         (all_files, uu____51192))))))
  
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
                let uu____51278 = FStar_Options.find_file fn  in
                match uu____51278 with
                | FStar_Pervasives_Native.None  ->
                    let uu____51284 =
                      let uu____51290 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____51290)
                       in
                    FStar_Errors.raise_err uu____51284
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____51320 =
          let uu____51324 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____51324  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____51320  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____51391 =
          let uu____51393 = deps_try_find dep_graph file_name  in
          uu____51393 = FStar_Pervasives_Native.None  in
        if uu____51391
        then
          let uu____51399 =
            let uu____51411 =
              let uu____51425 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____51425 file_name  in
            match uu____51411 with
            | FStar_Pervasives_Native.Some cached -> cached
            | FStar_Pervasives_Native.None  ->
                let r =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                ((r.direct_deps), (r.additional_roots),
                  (r.has_inline_for_extraction))
             in
          match uu____51399 with
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
                  let uu____51569 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____51569
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____51577 = FStar_List.unique deps1  in
                  { edges = uu____51577; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____51579 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____51579)))
        else ()  in
      FStar_Options.profile
        (fun uu____51589  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____51592  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____51624 =
            let uu____51630 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____51630)  in
          FStar_Errors.raise_err uu____51624)
          in
       let full_cycle_detection all_command_line_files =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let rec aux cycle filename =
           let node =
             let uu____51667 = deps_try_find dep_graph1 filename  in
             match uu____51667 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____51671 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____51671
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____51685 =
                           implementation_of file_system_map f  in
                         (match uu____51685 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51696 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____51702 =
                           implementation_of file_system_map f  in
                         (match uu____51702 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____51713 -> [x; UseImplementation f])
                     | uu____51717 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1383_51720 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____51722 =
                   dependences_of file_system_map dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____51722);
                deps_add_dep dep_graph1 filename
                  (let uu___1388_51732 = node  in
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
        let uu____51776 =
          FStar_Options.profile
            (fun uu____51795  ->
               let uu____51796 =
                 let uu____51798 = FStar_Options.codegen ()  in
                 uu____51798 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____51796)
            (fun uu____51804  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____51776 with
        | (all_files,uu____51822) ->
            ((let uu____51832 = FStar_Options.debug_any ()  in
              if uu____51832
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
          let uu____51902 = FStar_Options.find_file fn  in
          match uu____51902 with
          | FStar_Pervasives_Native.Some fn1 -> fn1
          | uu____51910 -> fn  in
        let digest_of_file1 fn2 =
          (let uu____51924 = FStar_Options.debug_any ()  in
           if uu____51924
           then
             FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
           else ());
          FStar_Util.digest_of_file fn2  in
        let module_name = lowercase_module_name fn1  in
        let source_hash = digest_of_file1 fn1  in
        let interface_hash =
          let uu____51943 =
            (is_implementation fn1) &&
              (has_interface file_system_map module_name)
             in
          if uu____51943
          then
            let uu____51954 =
              let uu____51961 =
                let uu____51963 =
                  let uu____51965 = interface_of file_system_map module_name
                     in
                  FStar_Option.get uu____51965  in
                digest_of_file1 uu____51963  in
              ("interface", uu____51961)  in
            [uu____51954]
          else []  in
        let binary_deps =
          let uu____51997 =
            dependences_of file_system_map deps1 all_cmd_line_files fn1  in
          FStar_All.pipe_right uu____51997
            (FStar_List.filter
               (fun fn2  ->
                  let uu____52012 =
                    (is_interface fn2) &&
                      (let uu____52015 = lowercase_module_name fn2  in
                       uu____52015 = module_name)
                     in
                  Prims.op_Negation uu____52012))
           in
        let binary_deps1 =
          FStar_List.sortWith
            (fun fn11  ->
               fun fn2  ->
                 let uu____52031 = lowercase_module_name fn11  in
                 let uu____52033 = lowercase_module_name fn2  in
                 FStar_String.compare uu____52031 uu____52033) binary_deps
           in
        let rec hash_deps out uu___436_52069 =
          match uu___436_52069 with
          | [] ->
              FStar_Util.Inr
                (FStar_List.append (("source", source_hash) ::
                   interface_hash) out)
          | fn2::deps2 ->
              let cache_fn = cache_file_name fn2  in
              let digest =
                if FStar_Util.file_exists cache_fn
                then
                  let uu____52136 = digest_of_file1 fn2  in
                  FStar_Pervasives_Native.Some uu____52136
                else FStar_Pervasives_Native.None  in
              (match digest with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____52157 = FStar_Options.debug_any ()  in
                     if uu____52157
                     then
                       let uu____52160 = FStar_Util.basename cache_fn  in
                       FStar_Util.print2 "%s: missed digest of file %s\n"
                         cache_file uu____52160
                     else ());
                    (let uu____52165 =
                       FStar_Util.format1 "cache file %s does not exist"
                         cache_fn
                        in
                     FStar_Util.Inl uu____52165))
               | FStar_Pervasives_Native.Some dig ->
                   let uu____52180 =
                     let uu____52189 =
                       let uu____52196 = lowercase_module_name fn2  in
                       (uu____52196, dig)  in
                     uu____52189 :: out  in
                   hash_deps uu____52180 deps2)
           in
        hash_deps [] binary_deps1
  
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig  ->
    let uu____52236 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____52262  ->
              match uu____52262 with
              | (m,d) ->
                  let uu____52276 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____52276))
       in
    FStar_All.pipe_right uu____52236 (FStar_String.concat "\n")
  
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
              let uu____52311 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____52311 FStar_Option.get  in
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
    let uu____52340 = deps.dep_graph  in
    match uu____52340 with
    | Deps deps1 ->
        let uu____52344 =
          let uu____52346 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____52364 =
                       let uu____52366 =
                         let uu____52368 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____52368
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____52366
                        in
                     uu____52364 :: out) []
             in
          FStar_All.pipe_right uu____52346 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____52344 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____52440 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____52440) ||
          (let uu____52447 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____52447)
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
            let uu____52490 =
              let uu____52494 = FStar_ST.op_Bang order  in ml_file ::
                uu____52494
               in
            FStar_ST.op_Colon_Equals order uu____52490
         in
      let rec aux uu___437_52557 =
        match uu___437_52557 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____52585 = deps_try_find deps.dep_graph file_name
                     in
                  (match uu____52585 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____52588 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____52588
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____52592;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____52601 = should_visit lc_module_name  in
              if uu____52601
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____52609 =
                    implementation_of deps.file_system_map lc_module_name  in
                  visit_file uu____52609);
                 (let uu____52614 =
                    interface_of deps.file_system_map lc_module_name  in
                  visit_file uu____52614);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____52626 = FStar_ST.op_Bang order  in
       FStar_List.rev uu____52626)
       in
    let sb =
      let uu____52657 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____52657  in
    let pr str =
      let uu____52667 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____52667  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____52720 =
          let uu____52722 =
            let uu____52726 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____52726  in
          FStar_Option.get uu____52722  in
        FStar_Util.replace_chars uu____52720 46 "_"  in
      let uu____52731 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____52731  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____52753 = output_file ".ml" f  in norm_path uu____52753  in
    let output_krml_file f =
      let uu____52765 = output_file ".krml" f  in norm_path uu____52765  in
    let output_cmx_file f =
      let uu____52777 = output_file ".cmx" f  in norm_path uu____52777  in
    let cache_file f =
      let uu____52789 = FStar_All.pipe_right f cache_file_name_internal  in
      FStar_All.pipe_right uu____52789
        (fun uu____52813  -> match uu____52813 with | (f1,b) -> norm_path f1)
       in
    FStar_All.pipe_right keys
      (FStar_List.iter
         (fun file_name  ->
            let process_one_key uu____52841 =
              let dep_node =
                let uu____52843 = deps_try_find deps.dep_graph file_name  in
                FStar_All.pipe_right uu____52843 FStar_Option.get  in
              let iface_deps =
                let uu____52853 = is_interface file_name  in
                if uu____52853
                then FStar_Pervasives_Native.None
                else
                  (let uu____52864 =
                     let uu____52868 = lowercase_module_name file_name  in
                     interface_of deps.file_system_map uu____52868  in
                   match uu____52864 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some iface ->
                       let uu____52880 =
                         let uu____52883 =
                           let uu____52884 =
                             deps_try_find deps.dep_graph iface  in
                           FStar_Option.get uu____52884  in
                         uu____52883.edges  in
                       FStar_Pervasives_Native.Some uu____52880)
                 in
              let iface_deps1 =
                FStar_Util.map_opt iface_deps
                  (FStar_List.filter
                     (fun iface_dep  ->
                        let uu____52901 =
                          FStar_Util.for_some (dep_subsumed_by iface_dep)
                            dep_node.edges
                           in
                        Prims.op_Negation uu____52901))
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
                  (fun uu____52961  -> FStar_String.concat "\\\n\t" files3)
                  (fun uu____52964  -> "Dependence analysis: concat files")
                 in
              let cache_file_name1 = cache_file file_name  in
              print_entry cache_file_name1 norm_f files4;
              (let uu____52970 =
                 let uu____52979 = FStar_Options.cmi ()  in
                 if uu____52979
                 then
                   FStar_Options.profile
                     (fun uu____52999  ->
                        topological_dependences_of deps.file_system_map
                          deps.dep_graph deps.interfaces_with_inlining
                          [file_name] true)
                     (fun uu____53004  ->
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
                    let uu____53048 =
                      FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                        (FStar_List.append fst_files fst_files_from_iface)
                       in
                    (uu____53048, false))
                  in
               match uu____52970 with
               | (all_fst_files_dep,widened) ->
                   let all_checked_fst_dep_files =
                     FStar_All.pipe_right all_fst_files_dep
                       (FStar_List.map cache_file)
                      in
                   let all_checked_fst_dep_files_string =
                     FStar_String.concat " \\\n\t" all_checked_fst_dep_files
                      in
                   let uu____53092 = is_implementation file_name  in
                   if uu____53092
                   then
                     ((let uu____53096 = (FStar_Options.cmi ()) && widened
                          in
                       if uu____53096
                       then
                         ((let uu____53100 = output_ml_file file_name  in
                           print_entry uu____53100 cache_file_name1
                             all_checked_fst_dep_files_string);
                          (let uu____53102 = output_krml_file file_name  in
                           print_entry uu____53102 cache_file_name1
                             all_checked_fst_dep_files_string))
                       else
                         ((let uu____53107 = output_ml_file file_name  in
                           print_entry uu____53107 cache_file_name1 "");
                          (let uu____53110 = output_krml_file file_name  in
                           print_entry uu____53110 cache_file_name1 "")));
                      (let cmx_files =
                         let extracted_fst_files =
                           FStar_All.pipe_right all_fst_files_dep
                             (FStar_List.filter
                                (fun df  ->
                                   (let uu____53135 =
                                      lowercase_module_name df  in
                                    let uu____53137 =
                                      lowercase_module_name file_name  in
                                    uu____53135 <> uu____53137) &&
                                     (let uu____53141 =
                                        lowercase_module_name df  in
                                      FStar_Options.should_extract
                                        uu____53141)))
                            in
                         FStar_All.pipe_right extracted_fst_files
                           (FStar_List.map output_cmx_file)
                          in
                       let uu____53151 =
                         let uu____53153 = lowercase_module_name file_name
                            in
                         FStar_Options.should_extract uu____53153  in
                       if uu____53151
                       then
                         let cmx_files1 =
                           FStar_String.concat "\\\n\t" cmx_files  in
                         let uu____53159 = output_cmx_file file_name  in
                         let uu____53161 = output_ml_file file_name  in
                         print_entry uu____53159 uu____53161 cmx_files1
                       else ()))
                   else
                     (let uu____53167 =
                        (let uu____53171 =
                           let uu____53173 = lowercase_module_name file_name
                              in
                           has_implementation deps.file_system_map
                             uu____53173
                            in
                         Prims.op_Negation uu____53171) &&
                          (is_interface file_name)
                         in
                      if uu____53167
                      then
                        let uu____53176 =
                          (FStar_Options.cmi ()) && (widened || true)  in
                        (if uu____53176
                         then
                           let uu____53180 = output_krml_file file_name  in
                           print_entry uu____53180 cache_file_name1
                             all_checked_fst_dep_files_string
                         else
                           (let uu____53184 = output_krml_file file_name  in
                            print_entry uu____53184 cache_file_name1 ""))
                      else ()))
               in
            FStar_Options.profile process_one_key
              (fun uu____53190  ->
                 FStar_Util.format1 "Dependence analysis: output key %s"
                   file_name)));
    (let all_fst_files =
       let uu____53196 =
         FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
       FStar_All.pipe_right uu____53196
         (FStar_Util.sort_with FStar_String.compare)
        in
     let all_ml_files =
       let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
       FStar_All.pipe_right all_fst_files
         (FStar_List.iter
            (fun fst_file  ->
               let mname = lowercase_module_name fst_file  in
               let uu____53237 = FStar_Options.should_extract mname  in
               if uu____53237
               then
                 let uu____53240 = output_ml_file fst_file  in
                 FStar_Util.smap_add ml_file_map mname uu____53240
               else ()));
       sort_output_files ml_file_map  in
     let all_krml_files =
       let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
       FStar_All.pipe_right keys
         (FStar_List.iter
            (fun fst_file  ->
               let mname = lowercase_module_name fst_file  in
               let uu____53267 = output_krml_file fst_file  in
               FStar_Util.smap_add krml_file_map mname uu____53267));
       sort_output_files krml_file_map  in
     let print_all tag files =
       pr tag;
       pr "=\\\n\t";
       FStar_List.iter (fun f  -> pr (norm_path f); pr " \\\n\t") files;
       pr "\n"  in
     print_all "ALL_FST_FILES" all_fst_files;
     print_all "ALL_ML_FILES" all_ml_files;
     print_all "ALL_KRML_FILES" all_krml_files;
     FStar_StringBuffer.output_channel FStar_Util.stdout sb)
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____53313 = FStar_Options.dep ()  in
    match uu____53313 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____53322  -> print_full deps)
          (fun uu____53324  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____53330 ->
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
         fun uu____53385  ->
           fun s  ->
             match uu____53385 with
             | (v0,v1) ->
                 let uu____53414 =
                   let uu____53416 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____53416  in
                 FStar_String.op_Hat s uu____53414) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____53437 =
        let uu____53439 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53439  in
      has_interface deps.file_system_map uu____53437
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____53455 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____53455  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____53466 =
                   let uu____53468 = module_name_of_file f  in
                   FStar_String.lowercase uu____53468  in
                 uu____53466 = m)))
  