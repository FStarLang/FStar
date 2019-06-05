open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____30 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____41 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____52 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____75 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____86 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____97 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____108 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____119 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____167 =
             (l > lext) &&
               (let uu____170 = FStar_String.substring f (l - lext) lext  in
                uu____170 = ext)
              in
           if uu____167
           then
             let uu____177 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____177
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____184 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____184 with
    | (FStar_Pervasives_Native.Some m)::uu____198 ->
        FStar_Pervasives_Native.Some m
    | uu____210 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____227 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____227 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____241 = is_interface f  in Prims.op_Negation uu____241 
let list_of_option :
  'Auu____248 .
    'Auu____248 FStar_Pervasives_Native.option -> 'Auu____248 Prims.list
  =
  fun uu___0_257  ->
    match uu___0_257 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____266 .
    ('Auu____266 FStar_Pervasives_Native.option * 'Auu____266
      FStar_Pervasives_Native.option) -> 'Auu____266 Prims.list
  =
  fun uu____281  ->
    match uu____281 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____309 =
      let uu____313 = FStar_Util.basename f  in
      check_and_strip_suffix uu____313  in
    match uu____309 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____320 =
          let uu____326 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____326)  in
        FStar_Errors.raise_err uu____320
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____340 = module_name_of_file f  in
    FStar_String.lowercase uu____340
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____353 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____353 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____356 ->
        let uu____359 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____359
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____399 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____422 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____445 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____468 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_486  ->
    match uu___1_486 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____505 . unit -> 'Auu____505 Prims.list =
  fun uu____508  -> [] 
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
type parsing_data_elt =
  | P_begin of FStar_Ident.lident 
  | P_inline_for_extraction 
  | P_open_module of (Prims.bool * FStar_Ident.lident) 
  | P_open_namespace of FStar_Ident.lident 
  | P_alias of (FStar_Ident.ident * FStar_Ident.lident) 
  | P_dep of (FStar_Ident.lident * Prims.bool) 
let (uu___is_P_begin : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_begin _0 -> true | uu____612 -> false
  
let (__proj__P_begin__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_begin _0 -> _0 
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_inline_for_extraction  -> true
    | uu____630 -> false
  
let (uu___is_P_open_module : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_open_module _0 -> true | uu____647 -> false
  
let (__proj__P_open_module__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_open_module _0 -> _0 
let (uu___is_P_open_namespace : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_open_namespace _0 -> true | uu____681 -> false
  
let (__proj__P_open_namespace__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_open_namespace _0 -> _0 
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_alias _0 -> true | uu____704 -> false
  
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_alias _0 -> _0 
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_dep _0 -> true | uu____740 -> false
  
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (FStar_Ident.lident * Prims.bool)) =
  fun projectee  -> match projectee with | P_dep _0 -> _0 
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee  -> match projectee with | Mk_pd _0 -> _0 
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun uu___2_798  ->
    match uu___2_798 with
    | P_begin lid ->
        let uu____801 = FStar_Ident.text_of_lid lid  in
        FStar_String.op_Hat "P_begin " uu____801
    | P_inline_for_extraction  -> "P_inline_for_extraction"
    | P_open_module (b,lid) ->
        let uu____809 =
          let uu____811 = FStar_Util.string_of_bool b  in
          let uu____813 =
            let uu____815 =
              let uu____817 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____817 ")"  in
            FStar_String.op_Hat ", " uu____815  in
          FStar_String.op_Hat uu____811 uu____813  in
        FStar_String.op_Hat "P_open_module (" uu____809
    | P_open_namespace lid ->
        let uu____823 = FStar_Ident.text_of_lid lid  in
        FStar_String.op_Hat "P_open_namespace " uu____823
    | P_alias (id1,lid) ->
        let uu____828 =
          let uu____830 = FStar_Ident.text_of_id id1  in
          let uu____832 =
            let uu____834 =
              let uu____836 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____836 ")"  in
            FStar_String.op_Hat ", " uu____834  in
          FStar_String.op_Hat uu____830 uu____832  in
        FStar_String.op_Hat "P_alias (" uu____828
    | P_dep (lid,b) ->
        let uu____845 =
          let uu____847 = FStar_Ident.text_of_lid lid  in
          let uu____849 =
            let uu____851 =
              let uu____853 = FStar_Util.string_of_bool b  in
              FStar_String.op_Hat uu____853 ")"  in
            FStar_String.op_Hat ", " uu____851  in
          FStar_String.op_Hat uu____847 uu____849  in
        FStar_String.op_Hat "P_dep (" uu____845
  
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___3_864  ->
    match uu___3_864 with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s  ->
                fun elt  ->
                  let uu____879 =
                    let uu____881 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt  in
                    FStar_String.op_Hat "; " uu____881  in
                  FStar_String.op_Hat s uu____879) "")
  
let (parsing_data_elt_eq :
  parsing_data_elt -> parsing_data_elt -> Prims.bool) =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (P_begin l1,P_begin l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction ,P_inline_for_extraction ) -> true
      | (P_open_module (b1,l1),P_open_module (b2,l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_open_namespace l1,P_open_namespace l2) ->
          FStar_Ident.lid_equals l1 l2
      | (P_alias (i1,l1),P_alias (i2,l2)) ->
          (let uu____921 = FStar_Ident.text_of_id i1  in
           let uu____923 = FStar_Ident.text_of_id i2  in
           uu____921 = uu____923) && (FStar_Ident.lid_equals l1 l2)
      | (P_dep (l1,b1),P_dep (l2,b2)) ->
          (FStar_Ident.lid_equals l1 l2) && (b1 = b2)
      | (uu____935,uu____936) -> false
  
let (empty_parsing_data : parsing_data) = Mk_pd [] 
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
  fun uu____1152  ->
    fun k  -> match uu____1152 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____1174  ->
    fun k  ->
      fun v1  -> match uu____1174 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____1189  -> match uu____1189 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____1201  ->
    let uu____1202 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____1202
  
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
  let uu____1260 = deps_empty ()  in
  let uu____1261 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____1273 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____1260 uu____1261 [] [] [] uu____1273 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___4_1286  ->
    match uu___4_1286 with
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
      let uu____1315 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1315 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1342) ->
          let uu____1364 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1364
      | FStar_Pervasives_Native.Some
          (uu____1367,FStar_Pervasives_Native.Some fn) ->
          let uu____1390 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1390
      | uu____1393 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1426 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1426 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1453) ->
          FStar_Pervasives_Native.Some iface
      | uu____1476 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1509 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1509 with
      | FStar_Pervasives_Native.Some
          (uu____1535,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1559 -> FStar_Pervasives_Native.None
  
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
      let uu____1620 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1620
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1640 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1640
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1675 =
      let uu____1679 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1679  in
    match uu____1675 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1690 =
            ((let uu____1694 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1694) &&
               (let uu____1700 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1700))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1703 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1703))
             in
          if uu____1690
          then
            let uu____1706 =
              let uu____1712 =
                let uu____1714 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1714
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1712)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1706
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1721 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1721
        then
          let uu____1727 =
            let uu____1733 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1733)
             in
          FStar_Errors.raise_err uu____1727
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____1769 = FStar_Util.smap_try_find memo x  in
    match uu____1769 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1796 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1796 FStar_Util.must
  
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
                      (let uu____1850 = lowercase_module_name fn  in
                       key = uu____1850)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1869 = interface_of_internal file_system_map key  in
              (match uu____1869 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1876 =
                     let uu____1882 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1882)  in
                   FStar_Errors.raise_err uu____1876
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1892 =
                (cmd_line_has_impl key) &&
                  (let uu____1895 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1895)
                 in
              if uu____1892
              then
                let uu____1902 = FStar_Options.expose_interfaces ()  in
                (if uu____1902
                 then
                   let uu____1906 =
                     let uu____1908 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____1908  in
                   maybe_use_cache_of uu____1906
                 else
                   (let uu____1915 =
                      let uu____1921 =
                        let uu____1923 =
                          let uu____1925 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____1925  in
                        let uu____1930 =
                          let uu____1932 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____1932  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1923 uu____1930
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1921)
                       in
                    FStar_Errors.raise_err uu____1915))
              else
                (let uu____1942 =
                   let uu____1944 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____1944  in
                 maybe_use_cache_of uu____1942)
          | PreferInterface key ->
              let uu____1951 = implementation_of_internal file_system_map key
                 in
              (match uu____1951 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1957 =
                     let uu____1963 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1963)
                      in
                   FStar_Errors.raise_err uu____1957
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____1973 = implementation_of_internal file_system_map key
                 in
              (match uu____1973 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1979 =
                     let uu____1985 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____1985)
                      in
                   FStar_Errors.raise_err uu____1979
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____1995 = implementation_of_internal file_system_map key
                 in
              (match uu____1995 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2001 =
                     let uu____2007 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2007)
                      in
                   FStar_Errors.raise_err uu____2001
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
          let uu____2068 = deps_try_find deps fn  in
          match uu____2068 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____2076;_} ->
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
    (let uu____2090 =
       let uu____2092 =
         let uu____2094 =
           let uu____2096 =
             let uu____2100 =
               let uu____2104 = deps_keys graph  in
               FStar_List.unique uu____2104  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____2118 =
                      let uu____2119 = deps_try_find graph k  in
                      FStar_Util.must uu____2119  in
                    uu____2118.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____2140 =
                      let uu____2142 = lowercase_module_name k  in
                      r uu____2142  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2140
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____2100
              in
           FStar_String.concat "\n" uu____2096  in
         FStar_String.op_Hat uu____2094 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____2092  in
     FStar_Util.write_file "dep.graph" uu____2090)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____2163  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____2189 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____2189  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____2229 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____2229
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____2266 =
              let uu____2272 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____2272)  in
            FStar_Errors.raise_err uu____2266)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____2335 = FStar_Util.smap_try_find map1 key  in
      match uu____2335 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2382 = is_interface full_path  in
          if uu____2382
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2431 = is_interface full_path  in
          if uu____2431
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2473 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2491  ->
          match uu____2491 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2473);
    FStar_List.iter
      (fun f  ->
         let uu____2510 = lowercase_module_name f  in add_entry uu____2510 f)
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
        (let uu____2542 =
           let uu____2546 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2546  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2582 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2582  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2542);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2702 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2702 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2725 = string_of_lid l last1  in
      FStar_String.lowercase uu____2725
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2734 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2734
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2756 =
        let uu____2758 =
          let uu____2760 =
            let uu____2762 =
              let uu____2766 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2766  in
            FStar_Util.must uu____2762  in
          FStar_String.lowercase uu____2760  in
        uu____2758 <> k'  in
      if uu____2756
      then
        let uu____2771 = FStar_Ident.range_of_lid lid  in
        let uu____2772 =
          let uu____2778 =
            let uu____2780 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2780 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2778)  in
        FStar_Errors.log_issue uu____2771 uu____2772
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2796 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2818 = FStar_Options.prims_basename ()  in
      let uu____2820 =
        let uu____2824 = FStar_Options.pervasives_basename ()  in
        let uu____2826 =
          let uu____2830 = FStar_Options.pervasives_native_basename ()  in
          [uu____2830]  in
        uu____2824 :: uu____2826  in
      uu____2818 :: uu____2820  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2873 =
         let uu____2876 = lowercase_module_name full_filename  in
         namespace_of_module uu____2876  in
       match uu____2873 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2915 -> d = d'
  
type record_t =
  {
  begin_module: FStar_Ident.lid -> unit ;
  set_interface_inlining: unit -> unit ;
  record_open_module: Prims.bool -> FStar_Ident.lident -> Prims.bool ;
  record_open_namespace: FStar_Ident.lident -> unit ;
  record_open: Prims.bool -> FStar_Ident.lident -> unit ;
  record_open_module_or_namespace: (FStar_Ident.lident * open_kind) -> unit ;
  record_module_alias: FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool ;
  add_dep_on_module: FStar_Ident.lident -> Prims.bool -> unit ;
  record_lid: FStar_Ident.lident -> unit ;
  get_deps: unit -> dependence Prims.list ;
  get_inline_for_extraction: unit -> Prims.bool ;
  get_parsing_data: unit -> parsing_data }
let (__proj__Mkrecord_t__item__begin_module :
  record_t -> FStar_Ident.lid -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> begin_module
  
let (__proj__Mkrecord_t__item__set_interface_inlining :
  record_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} ->
        set_interface_inlining
  
let (__proj__Mkrecord_t__item__record_open_module :
  record_t -> Prims.bool -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> record_open_module
  
let (__proj__Mkrecord_t__item__record_open_namespace :
  record_t -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} ->
        record_open_namespace
  
let (__proj__Mkrecord_t__item__record_open :
  record_t -> Prims.bool -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> record_open
  
let (__proj__Mkrecord_t__item__record_open_module_or_namespace :
  record_t -> (FStar_Ident.lident * open_kind) -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} ->
        record_open_module_or_namespace
  
let (__proj__Mkrecord_t__item__record_module_alias :
  record_t -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> record_module_alias
  
let (__proj__Mkrecord_t__item__add_dep_on_module :
  record_t -> FStar_Ident.lident -> Prims.bool -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> add_dep_on_module
  
let (__proj__Mkrecord_t__item__record_lid :
  record_t -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> record_lid
  
let (__proj__Mkrecord_t__item__get_deps :
  record_t -> unit -> dependence Prims.list) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> get_deps
  
let (__proj__Mkrecord_t__item__get_inline_for_extraction :
  record_t -> unit -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} ->
        get_inline_for_extraction
  
let (__proj__Mkrecord_t__item__get_parsing_data :
  record_t -> unit -> parsing_data) =
  fun projectee  ->
    match projectee with
    | { begin_module; set_interface_inlining; record_open_module;
        record_open_namespace; record_open; record_open_module_or_namespace;
        record_module_alias; add_dep_on_module; record_lid; get_deps;
        get_inline_for_extraction; get_parsing_data;_} -> get_parsing_data
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        (parsing_data * dependence Prims.list * Prims.bool * dependence
          Prims.list))
  =
  fun original_map  ->
    fun filename  ->
      fun get_parsing_data_from_cache  ->
        let record =
          let deps = FStar_Util.mk_ref []  in
          let has_inline_for_extraction = FStar_Util.mk_ref false  in
          let parsing_data = FStar_Util.mk_ref []  in
          let working_map = FStar_Util.smap_copy original_map  in
          let add_to_parsing_data elt =
            let uu____4249 =
              let uu____4251 =
                let uu____4253 = FStar_ST.op_Bang parsing_data  in
                FStar_List.existsML (fun e  -> parsing_data_elt_eq e elt)
                  uu____4253
                 in
              Prims.op_Negation uu____4251  in
            if uu____4249
            then
              let uu____4282 =
                let uu____4285 = FStar_ST.op_Bang parsing_data  in elt ::
                  uu____4285
                 in
              FStar_ST.op_Colon_Equals parsing_data uu____4282
            else ()  in
          let set_interface_inlining uu____4341 =
            add_to_parsing_data P_inline_for_extraction;
            (let uu____4343 = is_interface filename  in
             if uu____4343
             then FStar_ST.op_Colon_Equals has_inline_for_extraction true
             else ())
             in
          let add_dep deps1 d =
            let uu____4465 =
              let uu____4467 =
                let uu____4469 = FStar_ST.op_Bang deps1  in
                FStar_List.existsML (dep_subsumed_by d) uu____4469  in
              Prims.op_Negation uu____4467  in
            if uu____4465
            then
              let uu____4496 =
                let uu____4499 = FStar_ST.op_Bang deps1  in d :: uu____4499
                 in
              FStar_ST.op_Colon_Equals deps1 uu____4496
            else ()  in
          let dep_edge module_name is_friend =
            if is_friend
            then FriendImplementation module_name
            else PreferInterface module_name  in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true  in
            let uu____4590 = resolve_module_name original_or_working_map key
               in
            match uu____4590 with
            | FStar_Pervasives_Native.Some module_name ->
                (add_dep deps (dep_edge module_name is_friend); true)
            | uu____4600 -> false  in
          let record_open_module let_open lid =
            add_to_parsing_data (P_open_module (let_open, lid));
            (let uu____4621 =
               (let_open && (add_dependence_edge working_map lid false)) ||
                 ((Prims.op_Negation let_open) &&
                    (add_dependence_edge original_map lid false))
                in
             if uu____4621
             then true
             else
               (if let_open
                then
                  (let uu____4632 = FStar_Ident.range_of_lid lid  in
                   let uu____4633 =
                     let uu____4639 =
                       let uu____4641 = string_of_lid lid true  in
                       FStar_Util.format1 "Module not found: %s" uu____4641
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____4639)
                      in
                   FStar_Errors.log_issue uu____4632 uu____4633)
                else ();
                false))
             in
          let record_open_namespace lid =
            add_to_parsing_data (P_open_namespace lid);
            (let key = lowercase_join_longident lid true  in
             let r = enter_namespace original_map working_map key  in
             if Prims.op_Negation r
             then
               let uu____4662 = FStar_Ident.range_of_lid lid  in
               let uu____4663 =
                 let uu____4669 =
                   let uu____4671 = string_of_lid lid true  in
                   FStar_Util.format1
                     "No modules in namespace %s and no file with that name either"
                     uu____4671
                    in
                 (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                   uu____4669)
                  in
               FStar_Errors.log_issue uu____4662 uu____4663
             else ())
             in
          let record_open let_open lid =
            let uu____4691 = record_open_module let_open lid  in
            if uu____4691
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid
              else ()
             in
          let record_open_module_or_namespace uu____4708 =
            match uu____4708 with
            | (lid,kind) ->
                (match kind with
                 | Open_namespace  -> record_open_namespace lid
                 | Open_module  ->
                     let uu____4715 = record_open_module false lid  in ())
             in
          let record_module_alias ident lid =
            add_to_parsing_data (P_alias (ident, lid));
            (let key =
               let uu____4733 = FStar_Ident.text_of_id ident  in
               FStar_String.lowercase uu____4733  in
             let alias = lowercase_join_longident lid true  in
             let uu____4738 = FStar_Util.smap_try_find original_map alias  in
             match uu____4738 with
             | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                 (FStar_Util.smap_add working_map key deps_of_aliased_module;
                  (let uu____4795 =
                     let uu____4796 = lowercase_join_longident lid true  in
                     dep_edge uu____4796 false  in
                   add_dep deps uu____4795);
                  true)
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4812 = FStar_Ident.range_of_lid lid  in
                   let uu____4813 =
                     let uu____4819 =
                       FStar_Util.format1
                         "module not found in search path: %s\n" alias
                        in
                     (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                       uu____4819)
                      in
                   FStar_Errors.log_issue uu____4812 uu____4813);
                  false))
             in
          let add_dep_on_module module_name is_friend =
            add_to_parsing_data (P_dep (module_name, is_friend));
            (let uu____4839 =
               add_dependence_edge working_map module_name is_friend  in
             if uu____4839
             then ()
             else
               (let uu____4844 = FStar_Options.debug_any ()  in
                if uu____4844
                then
                  let uu____4847 = FStar_Ident.range_of_lid module_name  in
                  let uu____4848 =
                    let uu____4854 =
                      let uu____4856 = FStar_Ident.string_of_lid module_name
                         in
                      FStar_Util.format1 "Unbound module reference %s"
                        uu____4856
                       in
                    (FStar_Errors.Warning_UnboundModuleReference, uu____4854)
                     in
                  FStar_Errors.log_issue uu____4847 uu____4848
                else ()))
             in
          let record_lid lid =
            match lid.FStar_Ident.ns with
            | [] -> ()
            | uu____4868 ->
                let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                   in
                add_dep_on_module module_name false
             in
          let begin_module lid =
            add_to_parsing_data (P_begin lid);
            if (FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")
            then
              (let uu____4882 =
                 let uu____4884 = namespace_of_lid lid  in
                 enter_namespace original_map working_map uu____4884  in
               ())
            else ()  in
          {
            begin_module;
            set_interface_inlining;
            record_open_module;
            record_open_namespace;
            record_open;
            record_open_module_or_namespace;
            record_module_alias;
            add_dep_on_module;
            record_lid;
            get_deps = (fun uu____4889  -> FStar_ST.op_Bang deps);
            get_inline_for_extraction =
              (fun uu____4914  -> FStar_ST.op_Bang has_inline_for_extraction);
            get_parsing_data =
              (fun uu____4938  ->
                 let uu____4939 =
                   let uu____4942 = FStar_ST.op_Bang parsing_data  in
                   FStar_All.pipe_right uu____4942 FStar_List.rev  in
                 Mk_pd uu____4939)
          }  in
        let read_parsing_data_from_cache pd =
          match pd with
          | Mk_pd l ->
              FStar_All.pipe_right l
                (FStar_List.iter
                   (fun d  ->
                      match d with
                      | P_begin lid -> record.begin_module lid
                      | P_inline_for_extraction  ->
                          record.set_interface_inlining ()
                      | P_open_module (b,lid) ->
                          let uu____4991 = record.record_open_module b lid
                             in
                          ()
                      | P_open_namespace lid ->
                          record.record_open_namespace lid
                      | P_alias (id1,lid) ->
                          let uu____4996 = record.record_module_alias id1 lid
                             in
                          ()
                      | P_dep (lid,b) -> record.add_dep_on_module lid b))
           in
        let mo_roots =
          let mname = lowercase_module_name filename  in
          let uu____5007 =
            (is_interface filename) &&
              (has_implementation original_map mname)
             in
          if uu____5007 then [UseImplementation mname] else []  in
        let print_dependence_list deps =
          FStar_List.fold_left
            (fun s  ->
               fun d  ->
                 let uu____5032 =
                   let uu____5034 = dep_to_string d  in
                   FStar_String.op_Hat "::" uu____5034  in
                 FStar_String.op_Hat s uu____5032) "" deps
           in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____5044 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____5044
        then
          ((let uu____5064 = FStar_Options.debug_any ()  in
            if uu____5064
            then
              FStar_Util.print1
                "Reading parsing data for %s from its checked file\n"
                filename
            else ());
           (let uu____5071 =
              FStar_All.pipe_right data_from_cache FStar_Util.must  in
            FStar_All.pipe_right uu____5071 read_parsing_data_from_cache);
           (let uu____5075 =
              let uu____5077 = record.get_deps ()  in
              print_dependence_list uu____5077  in
            FStar_Util.print2
              "Dependences for %s as read from the cache:%s\n" filename
              uu____5075);
           (let uu____5082 =
              let uu____5084 =
                FStar_All.pipe_right data_from_cache FStar_Util.must  in
              str_of_parsing_data uu____5084  in
            FStar_Util.print2
              "Parsing data for %s as read from the cache:%s\n" filename
              uu____5082);
           (let uu____5088 =
              FStar_All.pipe_right data_from_cache FStar_Util.must  in
            let uu____5091 = record.get_deps ()  in
            let uu____5094 = record.get_inline_for_extraction ()  in
            (uu____5088, uu____5091, uu____5094, mo_roots)))
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
              in
           let auto_open = hard_coded_dependencies filename  in
           FStar_List.iter record.record_open_module_or_namespace auto_open;
           (let rec collect_module uu___5_5227 =
              match uu___5_5227 with
              | FStar_Parser_AST.Module (lid,decls) ->
                  (check_module_declaration_against_filename lid filename;
                   record.begin_module lid;
                   collect_decls decls)
              | FStar_Parser_AST.Interface (lid,decls,uu____5238) ->
                  (check_module_declaration_against_filename lid filename;
                   record.begin_module lid;
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
                   then record.set_interface_inlining ()
                   else ()) decls
            
            and collect_decl d =
              match d with
              | FStar_Parser_AST.Include lid -> record.record_open false lid
              | FStar_Parser_AST.Open lid -> record.record_open false lid
              | FStar_Parser_AST.Friend lid ->
                  let uu____5265 =
                    let uu____5266 = lowercase_join_longident lid true  in
                    FStar_All.pipe_right uu____5266 FStar_Ident.lid_of_str
                     in
                  record.add_dep_on_module uu____5265 true
              | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                  let uu____5273 = record.record_module_alias ident lid  in
                  ()
              | FStar_Parser_AST.TopLevelLet (uu____5275,patterms) ->
                  FStar_List.iter
                    (fun uu____5297  ->
                       match uu____5297 with
                       | (pat,t) -> (collect_pattern pat; collect_term t))
                    patterms
              | FStar_Parser_AST.Main t -> collect_term t
              | FStar_Parser_AST.Splice (uu____5306,t) -> collect_term t
              | FStar_Parser_AST.Assume (uu____5312,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____5314;
                    FStar_Parser_AST.mdest = uu____5315;
                    FStar_Parser_AST.lift_op =
                      FStar_Parser_AST.NonReifiableLift t;_}
                  -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____5317;
                    FStar_Parser_AST.mdest = uu____5318;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                  -> collect_term t
              | FStar_Parser_AST.Val (uu____5320,t) -> collect_term t
              | FStar_Parser_AST.SubEffect
                  { FStar_Parser_AST.msource = uu____5322;
                    FStar_Parser_AST.mdest = uu____5323;
                    FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                      (t0,t1);_}
                  -> (collect_term t0; collect_term t1)
              | FStar_Parser_AST.Tycon (uu____5327,tc,ts) ->
                  (if tc
                   then record.record_lid FStar_Parser_Const.mk_class_lid
                   else ();
                   (let ts1 =
                      FStar_List.map
                        (fun uu____5366  ->
                           match uu____5366 with | (x,docnik) -> x) ts
                       in
                    FStar_List.iter collect_tycon ts1))
              | FStar_Parser_AST.Exception (uu____5379,t) ->
                  FStar_Util.iter_opt t collect_term
              | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
              | FStar_Parser_AST.Fsdoc uu____5386 -> ()
              | FStar_Parser_AST.Pragma uu____5387 -> ()
              | FStar_Parser_AST.TopLevelModule lid ->
                  (FStar_Util.incr num_of_toplevelmods;
                   (let uu____5390 =
                      let uu____5392 = FStar_ST.op_Bang num_of_toplevelmods
                         in
                      uu____5392 > (Prims.parse_int "1")  in
                    if uu____5390
                    then
                      let uu____5417 =
                        let uu____5423 =
                          let uu____5425 = string_of_lid lid true  in
                          FStar_Util.format1
                            "Automatic dependency analysis demands one module per file (module %s not supported)"
                            uu____5425
                           in
                        (FStar_Errors.Fatal_OneModulePerFile, uu____5423)  in
                      let uu____5430 = FStar_Ident.range_of_lid lid  in
                      FStar_Errors.raise_error uu____5417 uu____5430
                    else ()))
            
            and collect_tycon uu___6_5433 =
              match uu___6_5433 with
              | FStar_Parser_AST.TyconAbstract (uu____5434,binders,k) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term)
              | FStar_Parser_AST.TyconAbbrev (uu____5446,binders,k,t) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   collect_term t)
              | FStar_Parser_AST.TyconRecord
                  (uu____5460,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____5506  ->
                        match uu____5506 with
                        | (uu____5515,t,uu____5517) -> collect_term t)
                     identterms)
              | FStar_Parser_AST.TyconVariant
                  (uu____5522,binders,k,identterms) ->
                  (collect_binders binders;
                   FStar_Util.iter_opt k collect_term;
                   FStar_List.iter
                     (fun uu____5584  ->
                        match uu____5584 with
                        | (uu____5598,t,uu____5600,uu____5601) ->
                            FStar_Util.iter_opt t collect_term) identterms)
            
            and collect_effect_decl uu___7_5612 =
              match uu___7_5612 with
              | FStar_Parser_AST.DefineEffect (uu____5613,binders,t,decls) ->
                  (collect_binders binders;
                   collect_term t;
                   collect_decls decls)
              | FStar_Parser_AST.RedefineEffect (uu____5627,binders,t) ->
                  (collect_binders binders; collect_term t)
            
            and collect_binders binders =
              FStar_List.iter collect_binder binders
            
            and collect_binder b =
              collect_aqual b.FStar_Parser_AST.aqual;
              (match b with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____5640,t);
                   FStar_Parser_AST.brange = uu____5642;
                   FStar_Parser_AST.blevel = uu____5643;
                   FStar_Parser_AST.aqual = uu____5644;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____5647,t);
                   FStar_Parser_AST.brange = uu____5649;
                   FStar_Parser_AST.blevel = uu____5650;
                   FStar_Parser_AST.aqual = uu____5651;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____5655;
                   FStar_Parser_AST.blevel = uu____5656;
                   FStar_Parser_AST.aqual = uu____5657;_} -> collect_term t
               | uu____5660 -> ())
            
            and collect_aqual uu___8_5661 =
              match uu___8_5661 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                  collect_term t
              | uu____5665 -> ()
            
            and collect_term t = collect_term' t.FStar_Parser_AST.tm
            
            and collect_constant uu___9_5669 =
              match uu___9_5669 with
              | FStar_Const.Const_int
                  (uu____5670,FStar_Pervasives_Native.Some
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
                  let uu____5697 =
                    let uu____5698 = FStar_Util.format2 "fstar.%sint%s" u w
                       in
                    FStar_All.pipe_right uu____5698 FStar_Ident.lid_of_str
                     in
                  record.add_dep_on_module uu____5697 false
              | FStar_Const.Const_char uu____5703 ->
                  let uu____5705 =
                    FStar_All.pipe_right "fstar.char" FStar_Ident.lid_of_str
                     in
                  record.add_dep_on_module uu____5705 false
              | FStar_Const.Const_float uu____5709 ->
                  let uu____5710 =
                    FStar_All.pipe_right "fstar.float" FStar_Ident.lid_of_str
                     in
                  record.add_dep_on_module uu____5710 false
              | uu____5714 -> ()
            
            and collect_term' uu___12_5715 =
              match uu___12_5715 with
              | FStar_Parser_AST.Wild  -> ()
              | FStar_Parser_AST.Const c -> collect_constant c
              | FStar_Parser_AST.Op (s,ts) ->
                  ((let uu____5724 =
                      let uu____5726 = FStar_Ident.text_of_id s  in
                      uu____5726 = "@"  in
                    if uu____5724
                    then
                      let uu____5731 =
                        let uu____5732 =
                          let uu____5733 =
                            FStar_Ident.path_of_text
                              "FStar.List.Tot.Base.append"
                             in
                          FStar_Ident.lid_of_path uu____5733
                            FStar_Range.dummyRange
                           in
                        FStar_Parser_AST.Name uu____5732  in
                      collect_term' uu____5731
                    else ());
                   FStar_List.iter collect_term ts)
              | FStar_Parser_AST.Tvar uu____5737 -> ()
              | FStar_Parser_AST.Uvar uu____5738 -> ()
              | FStar_Parser_AST.Var lid -> record.record_lid lid
              | FStar_Parser_AST.Projector (lid,uu____5741) ->
                  record.record_lid lid
              | FStar_Parser_AST.Discrim lid -> record.record_lid lid
              | FStar_Parser_AST.Name lid -> record.record_lid lid
              | FStar_Parser_AST.Construct (lid,termimps) ->
                  (record.record_lid lid;
                   FStar_List.iter
                     (fun uu____5766  ->
                        match uu____5766 with
                        | (t,uu____5772) -> collect_term t) termimps)
              | FStar_Parser_AST.Abs (pats,t) ->
                  (collect_patterns pats; collect_term t)
              | FStar_Parser_AST.App (t1,t2,uu____5782) ->
                  (collect_term t1; collect_term t2)
              | FStar_Parser_AST.Let (uu____5784,patterms,t) ->
                  (FStar_List.iter
                     (fun uu____5834  ->
                        match uu____5834 with
                        | (attrs_opt,(pat,t1)) ->
                            ((let uu____5863 =
                                FStar_Util.map_opt attrs_opt
                                  (FStar_List.iter collect_term)
                                 in
                              ());
                             collect_pattern pat;
                             collect_term t1)) patterms;
                   collect_term t)
              | FStar_Parser_AST.LetOpen (lid,t) ->
                  (record.record_open true lid; collect_term t)
              | FStar_Parser_AST.Bind (uu____5873,t1,t2) ->
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
                     (fun uu____5969  ->
                        match uu____5969 with
                        | (uu____5974,t1) -> collect_term t1) idterms)
              | FStar_Parser_AST.Project (t,uu____5977) -> collect_term t
              | FStar_Parser_AST.Product (binders,t) ->
                  (collect_binders binders; collect_term t)
              | FStar_Parser_AST.Sum (binders,t) ->
                  (FStar_List.iter
                     (fun uu___10_6006  ->
                        match uu___10_6006 with
                        | FStar_Util.Inl b -> collect_binder b
                        | FStar_Util.Inr t1 -> collect_term t1) binders;
                   collect_term t)
              | FStar_Parser_AST.QForall (binders,(uu____6014,ts),t) ->
                  (collect_binders binders;
                   FStar_List.iter (FStar_List.iter collect_term) ts;
                   collect_term t)
              | FStar_Parser_AST.QExists (binders,(uu____6048,ts),t) ->
                  (collect_binders binders;
                   FStar_List.iter (FStar_List.iter collect_term) ts;
                   collect_term t)
              | FStar_Parser_AST.Refine (binder,t) ->
                  (collect_binder binder; collect_term t)
              | FStar_Parser_AST.NamedTyp (uu____6084,t) -> collect_term t
              | FStar_Parser_AST.Paren t -> collect_term t
              | FStar_Parser_AST.Requires (t,uu____6088) -> collect_term t
              | FStar_Parser_AST.Ensures (t,uu____6096) -> collect_term t
              | FStar_Parser_AST.Labeled (t,uu____6104,uu____6105) ->
                  collect_term t
              | FStar_Parser_AST.Quote (t,uu____6111) -> collect_term t
              | FStar_Parser_AST.Antiquote t -> collect_term t
              | FStar_Parser_AST.VQuote t -> collect_term t
              | FStar_Parser_AST.Attributes cattributes ->
                  FStar_List.iter collect_term cattributes
              | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                  ((let uu____6125 = FStar_Ident.lid_of_str "FStar.Calc"  in
                    record.add_dep_on_module uu____6125 false);
                   collect_term rel;
                   collect_term init1;
                   FStar_List.iter
                     (fun uu___11_6136  ->
                        match uu___11_6136 with
                        | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                            (collect_term rel1;
                             collect_term just;
                             collect_term next)) steps)
            
            and collect_patterns ps = FStar_List.iter collect_pattern ps
            
            and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
            
            and collect_pattern' uu___13_6146 =
              match uu___13_6146 with
              | FStar_Parser_AST.PatVar (uu____6147,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatTvar (uu____6153,aqual) ->
                  collect_aqual aqual
              | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
              | FStar_Parser_AST.PatOp uu____6162 -> ()
              | FStar_Parser_AST.PatConst uu____6163 -> ()
              | FStar_Parser_AST.PatApp (p,ps) ->
                  (collect_pattern p; collect_patterns ps)
              | FStar_Parser_AST.PatName uu____6171 -> ()
              | FStar_Parser_AST.PatList ps -> collect_patterns ps
              | FStar_Parser_AST.PatOr ps -> collect_patterns ps
              | FStar_Parser_AST.PatTuple (ps,uu____6179) ->
                  collect_patterns ps
              | FStar_Parser_AST.PatRecord lidpats ->
                  FStar_List.iter
                    (fun uu____6200  ->
                       match uu____6200 with
                       | (uu____6205,p) -> collect_pattern p) lidpats
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.None )) ->
                  (collect_pattern p; collect_term t)
              | FStar_Parser_AST.PatAscribed
                  (p,(t,FStar_Pervasives_Native.Some tac)) ->
                  (collect_pattern p; collect_term t; collect_term tac)
            
            and collect_branches bs = FStar_List.iter collect_branch bs
            
            and collect_branch uu____6250 =
              match uu____6250 with
              | (pat,t1,t2) ->
                  (collect_pattern pat;
                   FStar_Util.iter_opt t1 collect_term;
                   collect_term t2)
             in
            let uu____6268 = FStar_Parser_Driver.parse_file filename  in
            match uu____6268 with
            | (ast,uu____6294) ->
                (collect_module ast;
                 (let uu____6311 = FStar_Options.debug_any ()  in
                  if uu____6311
                  then
                    ((let uu____6315 =
                        let uu____6317 = record.get_deps ()  in
                        print_dependence_list uu____6317  in
                      FStar_Util.print2
                        "For file %s Dependences as NOT read from the cache:%s\n"
                        filename uu____6315);
                     (let uu____6321 =
                        let uu____6323 = record.get_parsing_data ()  in
                        str_of_parsing_data uu____6323  in
                      FStar_Util.print2
                        "For file %s Parsing data as NOT read from the cache:%s\n"
                        filename uu____6321))
                  else ());
                 (let uu____6327 = record.get_parsing_data ()  in
                  let uu____6328 = record.get_deps ()  in
                  let uu____6331 = record.get_inline_for_extraction ()  in
                  (uu____6327, uu____6328, uu____6331, mo_roots)))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____6354 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____6354 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____6476 = dep_graph  in
    match uu____6476 with
    | Deps g -> let uu____6480 = FStar_Util.smap_copy g  in Deps uu____6480
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____6625 filename =
              match uu____6625 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____6666 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____6666  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____6697 = FStar_Options.debug_any ()  in
                         if uu____6697
                         then
                           let uu____6700 =
                             let uu____6702 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____6702  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____6700
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1000_6713 = dep_node  in
                           { edges = (uu___1000_6713.edges); color = Gray });
                        (let uu____6714 =
                           let uu____6725 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____6725
                            in
                         match uu____6714 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1006_6761 = dep_node  in
                                 {
                                   edges = (uu___1006_6761.edges);
                                   color = Black
                                 });
                              (let uu____6763 = FStar_Options.debug_any ()
                                  in
                               if uu____6763
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____6769 =
                                 let uu____6773 =
                                   FStar_List.collect
                                     (fun uu___14_6780  ->
                                        match uu___14_6780 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____6773 all_friends1
                                  in
                               (uu____6769, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____6846 = FStar_Options.debug_any ()  in
             if uu____6846
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____6875 = deps  in
               match uu____6875 with
               | Deps dg ->
                   let uu____6879 = deps_empty ()  in
                   (match uu____6879 with
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
                                  | uu____6929 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____6937  ->
                                  let uu____6939 =
                                    let uu___1041_6940 = dep_node  in
                                    let uu____6941 = widen_one dep_node.edges
                                       in
                                    { edges = uu____6941; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____6939)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____6943 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____6943
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____6948 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____6948 with
             | (friends,all_files_0) ->
                 ((let uu____6991 = FStar_Options.debug_any ()  in
                   if uu____6991
                   then
                     let uu____6994 =
                       let uu____6996 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____6996  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____6994
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____7015 =
                     (let uu____7027 = FStar_Options.debug_any ()  in
                      if uu____7027
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____7015 with
                   | (uu____7050,all_files) ->
                       ((let uu____7065 = FStar_Options.debug_any ()  in
                         if uu____7065
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____7072 = FStar_ST.op_Bang widened  in
                         (all_files, uu____7072))))))
  
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
                let uu____7158 = FStar_Options.find_file fn  in
                match uu____7158 with
                | FStar_Pervasives_Native.None  ->
                    let uu____7164 =
                      let uu____7170 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____7170)
                       in
                    FStar_Errors.raise_err uu____7164
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____7200 =
          let uu____7204 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____7204  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____7200  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____7271 =
          let uu____7273 = deps_try_find dep_graph file_name  in
          uu____7273 = FStar_Pervasives_Native.None  in
        if uu____7271
        then
          let uu____7279 =
            let uu____7295 =
              let uu____7309 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____7309 file_name  in
            match uu____7295 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None  ->
                let uu____7439 =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                (match uu____7439 with
                 | (parsing_data,deps,needs_interface_inlining,additional_roots)
                     ->
                     (parsing_data,
                       (deps, additional_roots, needs_interface_inlining)))
             in
          match uu____7279 with
          | (parsing_data,(deps,mo_roots,needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name parsing_data;
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____7533 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____7533
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____7541 = FStar_List.unique deps1  in
                  { edges = uu____7541; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____7543 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____7543)))
        else ()  in
      FStar_Options.profile
        (fun uu____7553  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____7556  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____7588 =
            let uu____7594 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____7594)  in
          FStar_Errors.raise_err uu____7588)
          in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let mo_files = FStar_Util.mk_ref []  in
         let rec aux cycle filename =
           let node =
             let uu____7646 = deps_try_find dep_graph1 filename  in
             match uu____7646 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____7650 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____7650
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____7664 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____7664 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____7675 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____7681 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____7681 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____7692 -> [x; UseImplementation f])
                     | uu____7696 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1135_7699 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____7701 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____7701);
                deps_add_dep dep_graph1 filename
                  (let uu___1140_7712 = node  in
                   { edges = direct_deps; color = Black });
                (let uu____7713 = is_interface filename  in
                 if uu____7713
                 then
                   let uu____7716 =
                     let uu____7720 = lowercase_module_name filename  in
                     implementation_of_internal file_system_map1 uu____7720
                      in
                   FStar_Util.iter_opt uu____7716
                     (fun impl  ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu____7729 =
                            let uu____7733 = FStar_ST.op_Bang mo_files  in
                            impl :: uu____7733  in
                          FStar_ST.op_Colon_Equals mo_files uu____7729
                        else ())
                 else ()))
            in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu____7795 = FStar_ST.op_Bang mo_files  in
          FStar_List.iter (aux []) uu____7795)
          in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____7867 =
          FStar_Options.profile
            (fun uu____7886  ->
               let uu____7887 =
                 let uu____7889 = FStar_Options.codegen ()  in
                 uu____7889 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____7887)
            (fun uu____7895  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____7867 with
        | (all_files,uu____7913) ->
            ((let uu____7923 = FStar_Options.debug_any ()  in
              if uu____7923
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
    let uu____7976 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____8002  ->
              match uu____8002 with
              | (m,d) ->
                  let uu____8016 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____8016))
       in
    FStar_All.pipe_right uu____7976 (FStar_String.concat "\n")
  
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
              let uu____8051 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____8051 FStar_Option.get  in
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
    let uu____8080 = deps.dep_graph  in
    match uu____8080 with
    | Deps deps1 ->
        let uu____8084 =
          let uu____8086 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____8104 =
                       let uu____8106 =
                         let uu____8108 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____8108
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____8106
                        in
                     uu____8104 :: out) []
             in
          FStar_All.pipe_right uu____8086 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____8084 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____8180 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____8180) ||
          (let uu____8187 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____8187)
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
            let uu____8230 =
              let uu____8234 = FStar_ST.op_Bang order  in ml_file ::
                uu____8234
               in
            FStar_ST.op_Colon_Equals order uu____8230
         in
      let rec aux uu___15_8297 =
        match uu___15_8297 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____8325 = deps_try_find deps.dep_graph file_name  in
                  (match uu____8325 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8328 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____8328
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____8332;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____8341 = should_visit lc_module_name  in
              if uu____8341
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____8349 = implementation_of deps lc_module_name  in
                  visit_file uu____8349);
                 (let uu____8354 = interface_of deps lc_module_name  in
                  visit_file uu____8354);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____8366 = FStar_ST.op_Bang order  in FStar_List.rev uu____8366)
       in
    let sb =
      let uu____8397 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____8397  in
    let pr str =
      let uu____8407 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____8407  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____8460 =
          let uu____8462 =
            let uu____8466 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____8466  in
          FStar_Option.get uu____8462  in
        FStar_Util.replace_chars uu____8460 46 "_"  in
      let uu____8471 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____8471  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____8493 = output_file ".ml" f  in norm_path uu____8493  in
    let output_krml_file f =
      let uu____8505 = output_file ".krml" f  in norm_path uu____8505  in
    let output_cmx_file f =
      let uu____8517 = output_file ".cmx" f  in norm_path uu____8517  in
    let cache_file f =
      let uu____8529 = cache_file_name f  in norm_path uu____8529  in
    let all_checked_files =
      FStar_All.pipe_right keys
        (FStar_List.fold_left
           (fun all_checked_files  ->
              fun file_name  ->
                let process_one_key uu____8562 =
                  let dep_node =
                    let uu____8564 = deps_try_find deps.dep_graph file_name
                       in
                    FStar_All.pipe_right uu____8564 FStar_Option.get  in
                  let iface_deps =
                    let uu____8574 = is_interface file_name  in
                    if uu____8574
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____8585 =
                         let uu____8589 = lowercase_module_name file_name  in
                         interface_of deps uu____8589  in
                       match uu____8585 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some iface ->
                           let uu____8601 =
                             let uu____8604 =
                               let uu____8605 =
                                 deps_try_find deps.dep_graph iface  in
                               FStar_Option.get uu____8605  in
                             uu____8604.edges  in
                           FStar_Pervasives_Native.Some uu____8601)
                     in
                  let iface_deps1 =
                    FStar_Util.map_opt iface_deps
                      (FStar_List.filter
                         (fun iface_dep  ->
                            let uu____8622 =
                              FStar_Util.for_some (dep_subsumed_by iface_dep)
                                dep_node.edges
                               in
                            Prims.op_Negation uu____8622))
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
                      (fun uu____8682  -> FStar_String.concat "\\\n\t" files3)
                      (fun uu____8685  -> "Dependence analysis: concat files")
                     in
                  let cache_file_name1 = cache_file file_name  in
                  let all_checked_files1 =
                    let uu____8694 =
                      let uu____8696 =
                        let uu____8698 = module_name_of_file file_name  in
                        FStar_Options.should_be_already_cached uu____8698  in
                      Prims.op_Negation uu____8696  in
                    if uu____8694
                    then
                      (print_entry cache_file_name1 norm_f files4;
                       cache_file_name1
                       ::
                       all_checked_files)
                    else all_checked_files  in
                  let uu____8708 =
                    let uu____8717 = FStar_Options.cmi ()  in
                    if uu____8717
                    then
                      FStar_Options.profile
                        (fun uu____8737  ->
                           topological_dependences_of deps.file_system_map
                             deps.dep_graph deps.interfaces_with_inlining
                             [file_name] true)
                        (fun uu____8742  ->
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
                       let uu____8786 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           (FStar_List.append fst_files fst_files_from_iface)
                          in
                       (uu____8786, false))
                     in
                  match uu____8708 with
                  | (all_fst_files_dep,widened) ->
                      let all_checked_fst_dep_files =
                        FStar_All.pipe_right all_fst_files_dep
                          (FStar_List.map cache_file)
                         in
                      let all_checked_fst_dep_files_string =
                        FStar_String.concat " \\\n\t"
                          all_checked_fst_dep_files
                         in
                      ((let uu____8833 = is_implementation file_name  in
                        if uu____8833
                        then
                          ((let uu____8837 =
                              (FStar_Options.cmi ()) && widened  in
                            if uu____8837
                            then
                              ((let uu____8841 = output_ml_file file_name  in
                                print_entry uu____8841 cache_file_name1
                                  all_checked_fst_dep_files_string);
                               (let uu____8843 = output_krml_file file_name
                                   in
                                print_entry uu____8843 cache_file_name1
                                  all_checked_fst_dep_files_string))
                            else
                              ((let uu____8848 = output_ml_file file_name  in
                                print_entry uu____8848 cache_file_name1 "");
                               (let uu____8851 = output_krml_file file_name
                                   in
                                print_entry uu____8851 cache_file_name1 "")));
                           (let cmx_files =
                              let extracted_fst_files =
                                FStar_All.pipe_right all_fst_files_dep
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____8876 =
                                           lowercase_module_name df  in
                                         let uu____8878 =
                                           lowercase_module_name file_name
                                            in
                                         uu____8876 <> uu____8878) &&
                                          (let uu____8882 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____8882)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            let uu____8892 =
                              let uu____8894 =
                                lowercase_module_name file_name  in
                              FStar_Options.should_extract uu____8894  in
                            if uu____8892
                            then
                              let cmx_files1 =
                                FStar_String.concat "\\\n\t" cmx_files  in
                              let uu____8900 = output_cmx_file file_name  in
                              let uu____8902 = output_ml_file file_name  in
                              print_entry uu____8900 uu____8902 cmx_files1
                            else ()))
                        else
                          (let uu____8908 =
                             (let uu____8912 =
                                let uu____8914 =
                                  lowercase_module_name file_name  in
                                has_implementation deps.file_system_map
                                  uu____8914
                                 in
                              Prims.op_Negation uu____8912) &&
                               (is_interface file_name)
                              in
                           if uu____8908
                           then
                             let uu____8917 =
                               (FStar_Options.cmi ()) && (widened || true)
                                in
                             (if uu____8917
                              then
                                let uu____8921 = output_krml_file file_name
                                   in
                                print_entry uu____8921 cache_file_name1
                                  all_checked_fst_dep_files_string
                              else
                                (let uu____8925 = output_krml_file file_name
                                    in
                                 print_entry uu____8925 cache_file_name1 ""))
                           else ()));
                       all_checked_files1)
                   in
                FStar_Options.profile process_one_key
                  (fun uu____8934  ->
                     FStar_Util.format1 "Dependence analysis: output key %s"
                       file_name)) [])
       in
    let all_fst_files =
      let uu____8944 =
        FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
      FStar_All.pipe_right uu____8944
        (FStar_Util.sort_with FStar_String.compare)
       in
    let all_ml_files =
      let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right all_fst_files
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____8985 = FStar_Options.should_extract mname  in
              if uu____8985
              then
                let uu____8988 = output_ml_file fst_file  in
                FStar_Util.smap_add ml_file_map mname uu____8988
              else ()));
      sort_output_files ml_file_map  in
    let all_krml_files =
      let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____9015 = output_krml_file fst_file  in
              FStar_Util.smap_add krml_file_map mname uu____9015));
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
    let uu____9063 = FStar_Options.dep ()  in
    match uu____9063 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____9072  -> print_full deps)
          (fun uu____9074  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____9080 ->
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
         fun uu____9135  ->
           fun s  ->
             match uu____9135 with
             | (v0,v1) ->
                 let uu____9164 =
                   let uu____9166 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____9166  in
                 FStar_String.op_Hat s uu____9164) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____9187 =
        let uu____9189 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____9189  in
      has_interface deps.file_system_map uu____9187
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____9205 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____9205  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____9216 =
                   let uu____9218 = module_name_of_file f  in
                   FStar_String.lowercase uu____9218  in
                 uu____9216 = m)))
  