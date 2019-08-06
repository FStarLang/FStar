open Prims
let profile : 'Auu____14 . (unit -> 'Auu____14) -> 'Auu____14 =
  fun f  ->
    FStar_Profiling.profile f FStar_Pervasives_Native.None "Dependencies"
  
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____36 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____47 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____58 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____81 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____92 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  ->
    match projectee with | Black  -> true | uu____103 -> false
  
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____114 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____125 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____173 =
             (l > lext) &&
               (let uu____176 = FStar_String.substring f (l - lext) lext  in
                uu____176 = ext)
              in
           if uu____173
           then
             let uu____183 =
               FStar_String.substring f Prims.int_zero (l - lext)  in
             FStar_Pervasives_Native.Some uu____183
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____190 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____190 with
    | (FStar_Pervasives_Native.Some m)::uu____204 ->
        FStar_Pervasives_Native.Some m
    | uu____216 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____233 =
      FStar_String.get f ((FStar_String.length f) - Prims.int_one)  in
    uu____233 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____247 = is_interface f  in Prims.op_Negation uu____247 
let list_of_option :
  'Auu____254 .
    'Auu____254 FStar_Pervasives_Native.option -> 'Auu____254 Prims.list
  =
  fun uu___0_263  ->
    match uu___0_263 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____272 .
    ('Auu____272 FStar_Pervasives_Native.option * 'Auu____272
      FStar_Pervasives_Native.option) -> 'Auu____272 Prims.list
  =
  fun uu____287  ->
    match uu____287 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____315 =
      let uu____319 = FStar_Util.basename f  in
      check_and_strip_suffix uu____319  in
    match uu____315 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____326 =
          let uu____332 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____332)  in
        FStar_Errors.raise_err uu____326
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____346 = module_name_of_file f  in
    FStar_String.lowercase uu____346
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____359 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____359 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____362 ->
        let uu____365 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____365
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____405 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____428 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____451 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____474 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_492  ->
    match uu___1_492 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____511 . unit -> 'Auu____511 Prims.list =
  fun uu____514  -> [] 
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
  | P_begin_module of FStar_Ident.lident 
  | P_open of (Prims.bool * FStar_Ident.lident) 
  | P_open_module_or_namespace of (open_kind * FStar_Ident.lid) 
  | P_dep of (Prims.bool * FStar_Ident.lident) 
  | P_alias of (FStar_Ident.ident * FStar_Ident.lident) 
  | P_lid of FStar_Ident.lident 
  | P_inline_for_extraction 
let (uu___is_P_begin_module : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_begin_module _0 -> true | uu____627 -> false
  
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_begin_module _0 -> _0 
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_open _0 -> true | uu____651 -> false
  
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_open _0 -> _0 
let (uu___is_P_open_module_or_namespace : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_open_module_or_namespace _0 -> true
    | uu____689 -> false
  
let (__proj__P_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStar_Ident.lid)) =
  fun projectee  ->
    match projectee with | P_open_module_or_namespace _0 -> _0
  
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_dep _0 -> true | uu____725 -> false
  
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_dep _0 -> _0 
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_alias _0 -> true | uu____763 -> false
  
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_alias _0 -> _0 
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_lid _0 -> true | uu____794 -> false
  
let (__proj__P_lid__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_lid _0 -> _0 
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_inline_for_extraction  -> true
    | uu____812 -> false
  
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee  -> match projectee with | Mk_pd _0 -> _0 
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt  ->
    let str_of_open_kind uu___2_855 =
      match uu___2_855 with
      | Open_module  -> "P_open_module"
      | Open_namespace  -> "P_open_namespace"  in
    match elt with
    | P_begin_module lid ->
        let uu____861 =
          let uu____863 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____863 ")"  in
        FStar_String.op_Hat "P_begin_module (" uu____861
    | P_open (b,lid) ->
        let uu____871 =
          let uu____873 = FStar_Util.string_of_bool b  in
          let uu____875 =
            let uu____877 =
              let uu____879 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____879 ")"  in
            FStar_String.op_Hat ", " uu____877  in
          FStar_String.op_Hat uu____873 uu____875  in
        FStar_String.op_Hat "P_open (" uu____871
    | P_open_module_or_namespace (k,lid) ->
        let uu____886 =
          let uu____888 =
            let uu____890 =
              let uu____892 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____892 ")"  in
            FStar_String.op_Hat ", " uu____890  in
          FStar_String.op_Hat (str_of_open_kind k) uu____888  in
        FStar_String.op_Hat "P_open_module_or_namespace (" uu____886
    | P_dep (b,lid) ->
        let uu____901 =
          let uu____903 = FStar_Ident.text_of_lid lid  in
          let uu____905 =
            let uu____907 =
              let uu____909 = FStar_Util.string_of_bool b  in
              FStar_String.op_Hat uu____909 ")"  in
            FStar_String.op_Hat ", " uu____907  in
          FStar_String.op_Hat uu____903 uu____905  in
        FStar_String.op_Hat "P_dep (" uu____901
    | P_alias (id1,lid) ->
        let uu____916 =
          let uu____918 = FStar_Ident.text_of_id id1  in
          let uu____920 =
            let uu____922 =
              let uu____924 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____924 ")"  in
            FStar_String.op_Hat ", " uu____922  in
          FStar_String.op_Hat uu____918 uu____920  in
        FStar_String.op_Hat "P_alias (" uu____916
    | P_lid lid ->
        let uu____930 =
          let uu____932 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____932 ")"  in
        FStar_String.op_Hat "P_lid (" uu____930
    | P_inline_for_extraction  -> "P_inline_for_extraction"
  
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___3_943  ->
    match uu___3_943 with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s  ->
                fun elt  ->
                  let uu____958 =
                    let uu____960 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt  in
                    FStar_String.op_Hat "; " uu____960  in
                  FStar_String.op_Hat s uu____958) "")
  
let (parsing_data_elt_eq :
  parsing_data_elt -> parsing_data_elt -> Prims.bool) =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (P_begin_module l1,P_begin_module l2) -> FStar_Ident.lid_equals l1 l2
      | (P_open (b1,l1),P_open (b2,l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_open_module_or_namespace (k1,l1),P_open_module_or_namespace
         (k2,l2)) -> (k1 = k2) && (FStar_Ident.lid_equals l1 l2)
      | (P_dep (b1,l1),P_dep (b2,l2)) ->
          (b1 = b2) && (FStar_Ident.lid_equals l1 l2)
      | (P_alias (i1,l1),P_alias (i2,l2)) ->
          (let uu____1010 = FStar_Ident.text_of_id i1  in
           let uu____1012 = FStar_Ident.text_of_id i2  in
           uu____1010 = uu____1012) && (FStar_Ident.lid_equals l1 l2)
      | (P_lid l1,P_lid l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction ,P_inline_for_extraction ) -> true
      | (uu____1018,uu____1019) -> false
  
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
  fun uu____1235  ->
    fun k  -> match uu____1235 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____1257  ->
    fun k  ->
      fun v1  -> match uu____1257 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____1272  -> match uu____1272 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____1284  ->
    let uu____1285 = FStar_Util.smap_create (Prims.of_int (41))  in
    Deps uu____1285
  
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
  let uu____1343 = deps_empty ()  in
  let uu____1344 = FStar_Util.smap_create Prims.int_zero  in
  let uu____1356 = FStar_Util.smap_create Prims.int_zero  in
  mk_deps uu____1343 uu____1344 [] [] [] uu____1356 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___4_1369  ->
    match uu___4_1369 with
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
      let uu____1398 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1398 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1425) ->
          let uu____1447 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1447
      | FStar_Pervasives_Native.Some
          (uu____1450,FStar_Pervasives_Native.Some fn) ->
          let uu____1473 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1473
      | uu____1476 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1509 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1509 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1536) ->
          FStar_Pervasives_Native.Some iface
      | uu____1559 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1592 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1592 with
      | FStar_Pervasives_Native.Some
          (uu____1618,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1642 -> FStar_Pervasives_Native.None
  
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
      let uu____1703 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1703
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1723 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1723
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1758 =
      let uu____1762 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1762  in
    match uu____1758 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1773 =
            ((let uu____1777 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1777) &&
               (let uu____1783 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1783))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1786 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1786))
             in
          if uu____1773
          then
            let uu____1789 =
              let uu____1795 =
                let uu____1797 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1797
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1795)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1789
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1804 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1804
        then
          let uu____1810 =
            let uu____1816 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1816)
             in
          FStar_Errors.raise_err uu____1810
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.of_int (100))  in
  let memo1 f x =
    let uu____1852 = FStar_Util.smap_try_find memo x  in
    match uu____1852 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1879 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1879 FStar_Util.must
  
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
                      (let uu____1933 = lowercase_module_name fn  in
                       key = uu____1933)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1952 = interface_of_internal file_system_map key  in
              (match uu____1952 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1959 =
                     let uu____1965 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1965)  in
                   FStar_Errors.raise_err uu____1959
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1975 =
                (cmd_line_has_impl key) &&
                  (let uu____1978 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1978)
                 in
              if uu____1975
              then
                let uu____1985 = FStar_Options.expose_interfaces ()  in
                (if uu____1985
                 then
                   let uu____1989 =
                     let uu____1991 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____1991  in
                   maybe_use_cache_of uu____1989
                 else
                   (let uu____1998 =
                      let uu____2004 =
                        let uu____2006 =
                          let uu____2008 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____2008  in
                        let uu____2013 =
                          let uu____2015 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____2015  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____2006 uu____2013
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____2004)
                       in
                    FStar_Errors.raise_err uu____1998))
              else
                (let uu____2025 =
                   let uu____2027 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____2027  in
                 maybe_use_cache_of uu____2025)
          | PreferInterface key ->
              let uu____2034 = implementation_of_internal file_system_map key
                 in
              (match uu____2034 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2040 =
                     let uu____2046 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2046)
                      in
                   FStar_Errors.raise_err uu____2040
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____2056 = implementation_of_internal file_system_map key
                 in
              (match uu____2056 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2062 =
                     let uu____2068 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2068)
                      in
                   FStar_Errors.raise_err uu____2062
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____2078 = implementation_of_internal file_system_map key
                 in
              (match uu____2078 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2084 =
                     let uu____2090 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2090)
                      in
                   FStar_Errors.raise_err uu____2084
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
          let uu____2151 = deps_try_find deps fn  in
          match uu____2151 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____2159;_} ->
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
    (let uu____2173 =
       let uu____2175 =
         let uu____2177 =
           let uu____2179 =
             let uu____2183 =
               let uu____2187 = deps_keys graph  in
               FStar_List.unique uu____2187  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____2201 =
                      let uu____2202 = deps_try_find graph k  in
                      FStar_Util.must uu____2202  in
                    uu____2201.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____2223 =
                      let uu____2225 = lowercase_module_name k  in
                      r uu____2225  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2223
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____2183
              in
           FStar_String.concat "\n" uu____2179  in
         FStar_String.op_Hat uu____2177 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____2175  in
     FStar_Util.write_file "dep.graph" uu____2173)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____2246  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____2272 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____2272  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____2312 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____2312
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____2349 =
              let uu____2355 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____2355)  in
            FStar_Errors.raise_err uu____2349)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.of_int (41))  in
    let add_entry key full_path =
      let uu____2418 = FStar_Util.smap_try_find map1 key  in
      match uu____2418 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2465 = is_interface full_path  in
          if uu____2465
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2514 = is_interface full_path  in
          if uu____2514
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2556 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2574  ->
          match uu____2574 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2556);
    FStar_List.iter
      (fun f  ->
         let uu____2593 = lowercase_module_name f  in add_entry uu____2593 f)
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
        FStar_Util.smap_iter original_map
          (fun k  ->
             fun uu____2641  ->
               if FStar_Util.starts_with k prefix2
               then
                 let suffix =
                   FStar_String.substring k (FStar_String.length prefix2)
                     ((FStar_String.length k) - (FStar_String.length prefix2))
                    in
                 let filename =
                   let uu____2667 = FStar_Util.smap_try_find original_map k
                      in
                   FStar_Util.must uu____2667  in
                 (FStar_Util.smap_add working_map suffix filename;
                  FStar_ST.op_Colon_Equals found true)
               else ());
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2787 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2787 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2810 = string_of_lid l last1  in
      FStar_String.lowercase uu____2810
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2819 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2819
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2841 =
        let uu____2843 =
          let uu____2845 =
            let uu____2847 =
              let uu____2851 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2851  in
            FStar_Util.must uu____2847  in
          FStar_String.lowercase uu____2845  in
        uu____2843 <> k'  in
      if uu____2841
      then
        let uu____2856 = FStar_Ident.range_of_lid lid  in
        let uu____2857 =
          let uu____2863 =
            let uu____2865 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2865 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2863)  in
        FStar_Errors.log_issue uu____2856 uu____2857
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2881 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2903 = FStar_Options.prims_basename ()  in
      let uu____2905 =
        let uu____2909 = FStar_Options.pervasives_basename ()  in
        let uu____2911 =
          let uu____2915 = FStar_Options.pervasives_native_basename ()  in
          [uu____2915]  in
        uu____2909 :: uu____2911  in
      uu____2903 :: uu____2905  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2958 =
         let uu____2961 = lowercase_module_name full_filename  in
         namespace_of_module uu____2961  in
       match uu____2958 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____3000 -> d = d'
  
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
        let from_parsing_data pd original_map1 filename1 =
          let deps = FStar_Util.mk_ref []  in
          let has_inline_for_extraction = FStar_Util.mk_ref false  in
          let mo_roots =
            let mname = lowercase_module_name filename1  in
            let uu____3118 =
              (is_interface filename1) &&
                (has_implementation original_map1 mname)
               in
            if uu____3118 then [UseImplementation mname] else []  in
          let auto_open =
            let uu____3128 = hard_coded_dependencies filename1  in
            FStar_All.pipe_right uu____3128
              (FStar_List.map
                 (fun uu____3150  ->
                    match uu____3150 with
                    | (lid,k) -> P_open_module_or_namespace (k, lid)))
             in
          let working_map = FStar_Util.smap_copy original_map1  in
          let set_interface_inlining uu____3185 =
            let uu____3186 = is_interface filename1  in
            if uu____3186
            then FStar_ST.op_Colon_Equals has_inline_for_extraction true
            else ()  in
          let add_dep deps1 d =
            let uu____3308 =
              let uu____3310 =
                let uu____3312 = FStar_ST.op_Bang deps1  in
                FStar_List.existsML (dep_subsumed_by d) uu____3312  in
              Prims.op_Negation uu____3310  in
            if uu____3308
            then
              let uu____3339 =
                let uu____3342 = FStar_ST.op_Bang deps1  in d :: uu____3342
                 in
              FStar_ST.op_Colon_Equals deps1 uu____3339
            else ()  in
          let dep_edge module_name is_friend =
            if is_friend
            then FriendImplementation module_name
            else PreferInterface module_name  in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true  in
            let uu____3433 = resolve_module_name original_or_working_map key
               in
            match uu____3433 with
            | FStar_Pervasives_Native.Some module_name ->
                (add_dep deps (dep_edge module_name is_friend); true)
            | uu____3443 -> false  in
          let record_open_module let_open lid =
            let uu____3462 =
              (let_open && (add_dependence_edge working_map lid false)) ||
                ((Prims.op_Negation let_open) &&
                   (add_dependence_edge original_map1 lid false))
               in
            if uu____3462
            then true
            else
              (if let_open
               then
                 (let uu____3473 = FStar_Ident.range_of_lid lid  in
                  let uu____3474 =
                    let uu____3480 =
                      let uu____3482 = string_of_lid lid true  in
                      FStar_Util.format1 "Module not found: %s" uu____3482
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3480)
                     in
                  FStar_Errors.log_issue uu____3473 uu____3474)
               else ();
               false)
             in
          let record_open_namespace lid =
            let key = lowercase_join_longident lid true  in
            let r = enter_namespace original_map1 working_map key  in
            if Prims.op_Negation r
            then
              let uu____3502 = FStar_Ident.range_of_lid lid  in
              let uu____3503 =
                let uu____3509 =
                  let uu____3511 = string_of_lid lid true  in
                  FStar_Util.format1
                    "No modules in namespace %s and no file with that name either"
                    uu____3511
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3509)
                 in
              FStar_Errors.log_issue uu____3502 uu____3503
            else ()  in
          let record_open let_open lid =
            let uu____3531 = record_open_module let_open lid  in
            if uu____3531
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid
              else ()
             in
          let record_open_module_or_namespace uu____3548 =
            match uu____3548 with
            | (lid,kind) ->
                (match kind with
                 | Open_namespace  -> record_open_namespace lid
                 | Open_module  ->
                     let uu____3555 = record_open_module false lid  in ())
             in
          let record_module_alias ident lid =
            let key =
              let uu____3572 = FStar_Ident.text_of_id ident  in
              FStar_String.lowercase uu____3572  in
            let alias = lowercase_join_longident lid true  in
            let uu____3577 = FStar_Util.smap_try_find original_map1 alias  in
            match uu____3577 with
            | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                (FStar_Util.smap_add working_map key deps_of_aliased_module;
                 (let uu____3634 =
                    let uu____3635 = lowercase_join_longident lid true  in
                    dep_edge uu____3635 false  in
                  add_dep deps uu____3634);
                 true)
            | FStar_Pervasives_Native.None  ->
                ((let uu____3651 = FStar_Ident.range_of_lid lid  in
                  let uu____3652 =
                    let uu____3658 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3658)
                     in
                  FStar_Errors.log_issue uu____3651 uu____3652);
                 false)
             in
          let add_dep_on_module module_name is_friend =
            let uu____3676 =
              add_dependence_edge working_map module_name is_friend  in
            if uu____3676
            then ()
            else
              (let uu____3681 = FStar_Options.debug_any ()  in
               if uu____3681
               then
                 let uu____3684 = FStar_Ident.range_of_lid module_name  in
                 let uu____3685 =
                   let uu____3691 =
                     let uu____3693 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____3693
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____3691)
                    in
                 FStar_Errors.log_issue uu____3684 uu____3685
               else ())
             in
          let record_lid lid =
            match lid.FStar_Ident.ns with
            | [] -> ()
            | uu____3705 ->
                let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                   in
                add_dep_on_module module_name false
             in
          let begin_module lid =
            if (FStar_List.length lid.FStar_Ident.ns) > Prims.int_zero
            then
              let uu____3718 =
                let uu____3720 = namespace_of_lid lid  in
                enter_namespace original_map1 working_map uu____3720  in
              ()
            else ()  in
          (match pd with
           | Mk_pd l ->
               FStar_All.pipe_right (FStar_List.append auto_open l)
                 (FStar_List.iter
                    (fun elt  ->
                       match elt with
                       | P_begin_module lid -> begin_module lid
                       | P_open (b,lid) -> record_open b lid
                       | P_open_module_or_namespace (k,lid) ->
                           record_open_module_or_namespace (lid, k)
                       | P_dep (b,lid) -> add_dep_on_module lid b
                       | P_alias (id1,lid) ->
                           let uu____3746 = record_module_alias id1 lid  in
                           ()
                       | P_lid lid -> record_lid lid
                       | P_inline_for_extraction  ->
                           set_interface_inlining ())));
          (let uu____3749 = FStar_ST.op_Bang deps  in
           let uu____3775 = FStar_ST.op_Bang has_inline_for_extraction  in
           (uu____3749, uu____3775, mo_roots))
           in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____3809 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____3809
        then
          ((let uu____3829 = FStar_Options.debug_any ()  in
            if uu____3829
            then
              FStar_Util.print1
                "Reading the parsing data for %s from its checked file\n"
                filename
            else ());
           (let uu____3835 =
              let uu____3847 =
                FStar_All.pipe_right data_from_cache FStar_Util.must  in
              from_parsing_data uu____3847 original_map filename  in
            match uu____3835 with
            | (deps,has_inline_for_extraction,mo_roots) ->
                let uu____3876 =
                  FStar_All.pipe_right data_from_cache FStar_Util.must  in
                (uu____3876, deps, has_inline_for_extraction, mo_roots)))
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref Prims.int_zero  in
           let pd = FStar_Util.mk_ref []  in
           let add_to_parsing_data elt =
             let uu____3905 =
               let uu____3907 =
                 let uu____3909 = FStar_ST.op_Bang pd  in
                 FStar_List.existsML (fun e  -> parsing_data_elt_eq e elt)
                   uu____3909
                  in
               Prims.op_Negation uu____3907  in
             if uu____3905
             then
               let uu____3938 =
                 let uu____3941 = FStar_ST.op_Bang pd  in elt :: uu____3941
                  in
               FStar_ST.op_Colon_Equals pd uu____3938
             else ()  in
           let rec collect_module uu___5_4098 =
             match uu___5_4098 with
             | FStar_Parser_AST.Module (lid,decls) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
             | FStar_Parser_AST.Interface (lid,decls,uu____4109) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
           
           and collect_decls decls =
             FStar_List.iter
               (fun x  ->
                  collect_decl x.FStar_Parser_AST.d;
                  FStar_List.iter collect_term x.FStar_Parser_AST.attrs;
                  (match x.FStar_Parser_AST.d with
                   | FStar_Parser_AST.Val uu____4128 when
                       FStar_List.contains
                         FStar_Parser_AST.Inline_for_extraction
                         x.FStar_Parser_AST.quals
                       -> add_to_parsing_data P_inline_for_extraction
                   | uu____4133 -> ())) decls
           
           and collect_decl d =
             match d with
             | FStar_Parser_AST.Include lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Open lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Friend lid ->
                 let uu____4142 =
                   let uu____4143 =
                     let uu____4149 =
                       let uu____4150 = lowercase_join_longident lid true  in
                       FStar_All.pipe_right uu____4150 FStar_Ident.lid_of_str
                        in
                     (true, uu____4149)  in
                   P_dep uu____4143  in
                 add_to_parsing_data uu____4142
             | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStar_Parser_AST.TopLevelLet (uu____4158,patterms) ->
                 FStar_List.iter
                   (fun uu____4180  ->
                      match uu____4180 with
                      | (pat,t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStar_Parser_AST.Main t -> collect_term t
             | FStar_Parser_AST.Splice (uu____4189,t) -> collect_term t
             | FStar_Parser_AST.Assume (uu____4195,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4197;
                   FStar_Parser_AST.mdest = uu____4198;
                   FStar_Parser_AST.lift_op =
                     FStar_Parser_AST.NonReifiableLift t;_}
                 -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4200;
                   FStar_Parser_AST.mdest = uu____4201;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                 -> collect_term t
             | FStar_Parser_AST.Val (uu____4203,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4205;
                   FStar_Parser_AST.mdest = uu____4206;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                     (t0,t1);_}
                 -> (collect_term t0; collect_term t1)
             | FStar_Parser_AST.Tycon (uu____4210,tc,ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStar_Parser_Const.mk_class_lid)
                  else ();
                  (let ts1 =
                     FStar_List.map
                       (fun uu____4249  ->
                          match uu____4249 with | (x,docnik) -> x) ts
                      in
                   FStar_List.iter collect_tycon ts1))
             | FStar_Parser_AST.Exception (uu____4262,t) ->
                 FStar_Util.iter_opt t collect_term
             | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.Fsdoc uu____4269 -> ()
             | FStar_Parser_AST.Pragma uu____4270 -> ()
             | FStar_Parser_AST.TopLevelModule lid ->
                 (FStar_Util.incr num_of_toplevelmods;
                  (let uu____4273 =
                     let uu____4275 = FStar_ST.op_Bang num_of_toplevelmods
                        in
                     uu____4275 > Prims.int_one  in
                   if uu____4273
                   then
                     let uu____4300 =
                       let uu____4306 =
                         let uu____4308 = string_of_lid lid true  in
                         FStar_Util.format1
                           "Automatic dependency analysis demands one module per file (module %s not supported)"
                           uu____4308
                          in
                       (FStar_Errors.Fatal_OneModulePerFile, uu____4306)  in
                     let uu____4313 = FStar_Ident.range_of_lid lid  in
                     FStar_Errors.raise_error uu____4300 uu____4313
                   else ()))
           
           and collect_tycon uu___6_4316 =
             match uu___6_4316 with
             | FStar_Parser_AST.TyconAbstract (uu____4317,binders,k) ->
                 (collect_binders binders; FStar_Util.iter_opt k collect_term)
             | FStar_Parser_AST.TyconAbbrev (uu____4329,binders,k,t) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  collect_term t)
             | FStar_Parser_AST.TyconRecord (uu____4343,binders,k,identterms)
                 ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4389  ->
                       match uu____4389 with
                       | (uu____4398,t,uu____4400) -> collect_term t)
                    identterms)
             | FStar_Parser_AST.TyconVariant
                 (uu____4405,binders,k,identterms) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4467  ->
                       match uu____4467 with
                       | (uu____4481,t,uu____4483,uu____4484) ->
                           FStar_Util.iter_opt t collect_term) identterms)
           
           and collect_effect_decl uu___7_4495 =
             match uu___7_4495 with
             | FStar_Parser_AST.DefineEffect (uu____4496,binders,t,decls) ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStar_Parser_AST.RedefineEffect (uu____4510,binders,t) ->
                 (collect_binders binders; collect_term t)
           
           and collect_binders binders =
             FStar_List.iter collect_binder binders
           
           and collect_binder b =
             collect_aqual b.FStar_Parser_AST.aqual;
             (match b with
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                    (uu____4523,t);
                  FStar_Parser_AST.brange = uu____4525;
                  FStar_Parser_AST.blevel = uu____4526;
                  FStar_Parser_AST.aqual = uu____4527;_} -> collect_term t
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                    (uu____4530,t);
                  FStar_Parser_AST.brange = uu____4532;
                  FStar_Parser_AST.blevel = uu____4533;
                  FStar_Parser_AST.aqual = uu____4534;_} -> collect_term t
              | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu____4538;
                  FStar_Parser_AST.blevel = uu____4539;
                  FStar_Parser_AST.aqual = uu____4540;_} -> collect_term t
              | uu____4543 -> ())
           
           and collect_aqual uu___8_4544 =
             match uu___8_4544 with
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                 collect_term t
             | uu____4548 -> ()
           
           and collect_term t = collect_term' t.FStar_Parser_AST.tm
           
           and collect_constant uu___9_4552 =
             match uu___9_4552 with
             | FStar_Const.Const_int
                 (uu____4553,FStar_Pervasives_Native.Some (signedness,width))
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
                 let uu____4580 =
                   let uu____4581 =
                     let uu____4587 =
                       let uu____4588 =
                         FStar_Util.format2 "fstar.%sint%s" u w  in
                       FStar_All.pipe_right uu____4588 FStar_Ident.lid_of_str
                        in
                     (false, uu____4587)  in
                   P_dep uu____4581  in
                 add_to_parsing_data uu____4580
             | FStar_Const.Const_char uu____4594 ->
                 let uu____4596 =
                   let uu____4597 =
                     let uu____4603 =
                       FStar_All.pipe_right "fstar.char"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4603)  in
                   P_dep uu____4597  in
                 add_to_parsing_data uu____4596
             | FStar_Const.Const_float uu____4608 ->
                 let uu____4609 =
                   let uu____4610 =
                     let uu____4616 =
                       FStar_All.pipe_right "fstar.float"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4616)  in
                   P_dep uu____4610  in
                 add_to_parsing_data uu____4609
             | uu____4621 -> ()
           
           and collect_term' uu___12_4622 =
             match uu___12_4622 with
             | FStar_Parser_AST.Wild  -> ()
             | FStar_Parser_AST.Const c -> collect_constant c
             | FStar_Parser_AST.Op (s,ts) ->
                 ((let uu____4631 =
                     let uu____4633 = FStar_Ident.text_of_id s  in
                     uu____4633 = "@"  in
                   if uu____4631
                   then
                     let uu____4638 =
                       let uu____4639 =
                         let uu____4640 =
                           FStar_Ident.path_of_text
                             "FStar.List.Tot.Base.append"
                            in
                         FStar_Ident.lid_of_path uu____4640
                           FStar_Range.dummyRange
                          in
                       FStar_Parser_AST.Name uu____4639  in
                     collect_term' uu____4638
                   else ());
                  FStar_List.iter collect_term ts)
             | FStar_Parser_AST.Tvar uu____4644 -> ()
             | FStar_Parser_AST.Uvar uu____4645 -> ()
             | FStar_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Projector (lid,uu____4648) ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Construct (lid,termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStar_List.iter
                    (fun uu____4673  ->
                       match uu____4673 with
                       | (t,uu____4679) -> collect_term t) termimps)
             | FStar_Parser_AST.Abs (pats,t) ->
                 (collect_patterns pats; collect_term t)
             | FStar_Parser_AST.App (t1,t2,uu____4689) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Let (uu____4691,patterms,t) ->
                 (FStar_List.iter
                    (fun uu____4741  ->
                       match uu____4741 with
                       | (attrs_opt,(pat,t1)) ->
                           ((let uu____4770 =
                               FStar_Util.map_opt attrs_opt
                                 (FStar_List.iter collect_term)
                                in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStar_Parser_AST.LetOpen (lid,t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStar_Parser_AST.Bind (uu____4781,t1,t2) ->
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
                    (fun uu____4877  ->
                       match uu____4877 with
                       | (uu____4882,t1) -> collect_term t1) idterms)
             | FStar_Parser_AST.Project (t,uu____4885) -> collect_term t
             | FStar_Parser_AST.Product (binders,t) ->
                 (collect_binders binders; collect_term t)
             | FStar_Parser_AST.Sum (binders,t) ->
                 (FStar_List.iter
                    (fun uu___10_4914  ->
                       match uu___10_4914 with
                       | FStar_Util.Inl b -> collect_binder b
                       | FStar_Util.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStar_Parser_AST.QForall (binders,(uu____4922,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.QExists (binders,(uu____4956,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.Refine (binder,t) ->
                 (collect_binder binder; collect_term t)
             | FStar_Parser_AST.NamedTyp (uu____4992,t) -> collect_term t
             | FStar_Parser_AST.Paren t -> collect_term t
             | FStar_Parser_AST.Requires (t,uu____4996) -> collect_term t
             | FStar_Parser_AST.Ensures (t,uu____5004) -> collect_term t
             | FStar_Parser_AST.Labeled (t,uu____5012,uu____5013) ->
                 collect_term t
             | FStar_Parser_AST.Quote (t,uu____5019) -> collect_term t
             | FStar_Parser_AST.Antiquote t -> collect_term t
             | FStar_Parser_AST.VQuote t -> collect_term t
             | FStar_Parser_AST.Attributes cattributes ->
                 FStar_List.iter collect_term cattributes
             | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                 ((let uu____5033 =
                     let uu____5034 =
                       let uu____5040 = FStar_Ident.lid_of_str "FStar.Calc"
                          in
                       (false, uu____5040)  in
                     P_dep uu____5034  in
                   add_to_parsing_data uu____5033);
                  collect_term rel;
                  collect_term init1;
                  FStar_List.iter
                    (fun uu___11_5052  ->
                       match uu___11_5052 with
                       | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
           
           and collect_patterns ps = FStar_List.iter collect_pattern ps
           
           and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
           
           and collect_pattern' uu___13_5062 =
             match uu___13_5062 with
             | FStar_Parser_AST.PatVar (uu____5063,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatTvar (uu____5069,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
             | FStar_Parser_AST.PatOp uu____5078 -> ()
             | FStar_Parser_AST.PatConst uu____5079 -> ()
             | FStar_Parser_AST.PatApp (p,ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStar_Parser_AST.PatName uu____5087 -> ()
             | FStar_Parser_AST.PatList ps -> collect_patterns ps
             | FStar_Parser_AST.PatOr ps -> collect_patterns ps
             | FStar_Parser_AST.PatTuple (ps,uu____5095) ->
                 collect_patterns ps
             | FStar_Parser_AST.PatRecord lidpats ->
                 FStar_List.iter
                   (fun uu____5116  ->
                      match uu____5116 with
                      | (uu____5121,p) -> collect_pattern p) lidpats
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.None )) ->
                 (collect_pattern p; collect_term t)
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           
           and collect_branches bs = FStar_List.iter collect_branch bs
           
           and collect_branch uu____5166 =
             match uu____5166 with
             | (pat,t1,t2) ->
                 (collect_pattern pat;
                  FStar_Util.iter_opt t1 collect_term;
                  collect_term t2)
            in
           let uu____5184 = FStar_Parser_Driver.parse_file filename  in
           match uu____5184 with
           | (ast,uu____5210) ->
               (collect_module ast;
                (let pd1 =
                   let uu____5227 =
                     let uu____5230 = FStar_ST.op_Bang pd  in
                     FStar_List.rev uu____5230  in
                   Mk_pd uu____5227  in
                 let uu____5256 = from_parsing_data pd1 original_map filename
                    in
                 match uu____5256 with
                 | (deps,has_inline_for_extraction,mo_roots) ->
                     (pd1, deps, has_inline_for_extraction, mo_roots))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____5315 = FStar_Util.smap_create Prims.int_zero  in
  FStar_Util.mk_ref uu____5315 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5437 = dep_graph  in
    match uu____5437 with
    | Deps g -> let uu____5441 = FStar_Util.smap_copy g  in Deps uu____5441
  
let (widen_deps :
  module_name Prims.list ->
    dependence_graph ->
      files_for_module_name -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun friends  ->
    fun dep_graph  ->
      fun file_system_map  ->
        fun widened  ->
          let widened1 = FStar_Util.mk_ref widened  in
          let uu____5483 = dep_graph  in
          match uu____5483 with
          | Deps dg ->
              let uu____5492 = deps_empty ()  in
              (match uu____5492 with
               | Deps dg' ->
                   let widen_one deps =
                     FStar_All.pipe_right deps
                       (FStar_List.map
                          (fun d  ->
                             match d with
                             | PreferInterface m when
                                 (FStar_List.contains m friends) &&
                                   (has_implementation file_system_map m)
                                 ->
                                 (FStar_ST.op_Colon_Equals widened1 true;
                                  FriendImplementation m)
                             | uu____5547 -> d))
                      in
                   (FStar_Util.smap_fold dg
                      (fun filename  ->
                         fun dep_node  ->
                           fun uu____5555  ->
                             let uu____5557 =
                               let uu___984_5558 = dep_node  in
                               let uu____5559 = widen_one dep_node.edges  in
                               { edges = uu____5559; color = White }  in
                             FStar_Util.smap_add dg' filename uu____5557) ();
                    (let uu____5560 = FStar_ST.op_Bang widened1  in
                     (uu____5560, (Deps dg')))))
  
let (topological_dependences_of' :
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
          fun widened  ->
            let rec all_friend_deps_1 dep_graph1 cycle uu____5726 filename =
              match uu____5726 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____5767 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5767  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5798 = FStar_Options.debug_any ()  in
                         if uu____5798
                         then
                           let uu____5801 =
                             let uu____5803 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____5803  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5801
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___1006_5814 = dep_node  in
                           { edges = (uu___1006_5814.edges); color = Gray });
                        (let uu____5815 =
                           let uu____5826 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5826
                            in
                         match uu____5815 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___1012_5862 = dep_node  in
                                 {
                                   edges = (uu___1012_5862.edges);
                                   color = Black
                                 });
                              (let uu____5864 = FStar_Options.debug_any ()
                                  in
                               if uu____5864
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5870 =
                                 let uu____5874 =
                                   FStar_List.collect
                                     (fun uu___14_5881  ->
                                        match uu___14_5881 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____5874 all_friends1
                                  in
                               (uu____5870, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            let uu____5946 = all_friend_deps dep_graph [] ([], []) root_files
               in
            match uu____5946 with
            | (friends,all_files_0) ->
                ((let uu____5989 = FStar_Options.debug_any ()  in
                  if uu____5989
                  then
                    let uu____5992 =
                      let uu____5994 =
                        FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                          friends
                         in
                      FStar_String.concat ", " uu____5994  in
                    FStar_Util.print3
                      "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                      (FStar_String.concat ", " all_files_0) uu____5992
                      (FStar_String.concat ", " interfaces_needing_inlining)
                  else ());
                 (let uu____6012 =
                    widen_deps friends dep_graph file_system_map widened  in
                  match uu____6012 with
                  | (widened1,dep_graph1) ->
                      let uu____6030 =
                        (let uu____6042 = FStar_Options.debug_any ()  in
                         if uu____6042
                         then
                           FStar_Util.print_string
                             "==============Phase2==================\n"
                         else ());
                        all_friend_deps dep_graph1 [] ([], []) root_files  in
                      (match uu____6030 with
                       | (uu____6065,all_files) ->
                           ((let uu____6080 = FStar_Options.debug_any ()  in
                             if uu____6080
                             then
                               FStar_Util.print1
                                 "Phase2 complete: all_files = %s\n"
                                 (FStar_String.concat ", " all_files)
                             else ());
                            (all_files, widened1)))))
  
let (phase1 :
  files_for_module_name ->
    dependence_graph ->
      module_name Prims.list -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun file_system_map  ->
    fun dep_graph  ->
      fun interfaces_needing_inlining  ->
        fun for_extraction  ->
          (let uu____6126 = FStar_Options.debug_any ()  in
           if uu____6126
           then
             FStar_Util.print_string
               "==============Phase1==================\n"
           else ());
          (let widened = false  in
           let uu____6135 = (FStar_Options.cmi ()) && for_extraction  in
           if uu____6135
           then
             widen_deps interfaces_needing_inlining dep_graph file_system_map
               widened
           else (widened, dep_graph))
  
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
            let uu____6202 =
              phase1 file_system_map dep_graph interfaces_needing_inlining
                for_extraction
               in
            match uu____6202 with
            | (widened,dep_graph1) ->
                topological_dependences_of' file_system_map dep_graph1
                  interfaces_needing_inlining root_files widened
  
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
                let uu____6279 = FStar_Options.find_file fn  in
                match uu____6279 with
                | FStar_Pervasives_Native.None  ->
                    let uu____6285 =
                      let uu____6291 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____6291)
                       in
                    FStar_Errors.raise_err uu____6285
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____6321 =
          let uu____6325 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____6325  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6321  in
      let parse_results = FStar_Util.smap_create (Prims.of_int (40))  in
      let rec discover_one file_name =
        let uu____6392 =
          let uu____6394 = deps_try_find dep_graph file_name  in
          uu____6394 = FStar_Pervasives_Native.None  in
        if uu____6392
        then
          let uu____6400 =
            let uu____6416 =
              let uu____6430 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____6430 file_name  in
            match uu____6416 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None  ->
                let uu____6560 =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                (match uu____6560 with
                 | (parsing_data,deps,needs_interface_inlining,additional_roots)
                     ->
                     (parsing_data,
                       (deps, additional_roots, needs_interface_inlining)))
             in
          match uu____6400 with
          | (parsing_data,(deps,mo_roots,needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name parsing_data;
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____6654 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____6654
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____6662 = FStar_List.unique deps1  in
                  { edges = uu____6662; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____6664 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____6664)))
        else ()  in
      profile
        (fun uu____6674  -> FStar_List.iter discover_one all_cmd_line_files1);
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____6706 =
            let uu____6712 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____6712)  in
          FStar_Errors.raise_err uu____6706)
          in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let mo_files = FStar_Util.mk_ref []  in
         let rec aux cycle filename =
           let node =
             let uu____6764 = deps_try_find dep_graph1 filename  in
             match uu____6764 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____6768 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____6768
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____6782 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6782 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6793 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____6799 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6799 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6810 -> [x; UseImplementation f])
                     | uu____6814 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1133_6817 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____6819 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6819);
                deps_add_dep dep_graph1 filename
                  (let uu___1138_6830 = node  in
                   { edges = direct_deps; color = Black });
                (let uu____6831 = is_interface filename  in
                 if uu____6831
                 then
                   let uu____6834 =
                     let uu____6838 = lowercase_module_name filename  in
                     implementation_of_internal file_system_map1 uu____6838
                      in
                   FStar_Util.iter_opt uu____6834
                     (fun impl  ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu____6847 =
                            let uu____6851 = FStar_ST.op_Bang mo_files  in
                            impl :: uu____6851  in
                          FStar_ST.op_Colon_Equals mo_files uu____6847
                        else ())
                 else ()))
            in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu____6913 = FStar_ST.op_Bang mo_files  in
          FStar_List.iter (aux []) uu____6913)
          in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____6985 =
          profile
            (fun uu____7004  ->
               let uu____7005 =
                 let uu____7007 = FStar_Options.codegen ()  in
                 uu____7007 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____7005)
           in
        match uu____6985 with
        | (all_files,uu____7020) ->
            ((let uu____7030 = FStar_Options.debug_any ()  in
              if uu____7030
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
    let uu____7083 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____7109  ->
              match uu____7109 with
              | (m,d) ->
                  let uu____7123 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____7123))
       in
    FStar_All.pipe_right uu____7083 (FStar_String.concat "\n")
  
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
              let uu____7158 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____7158 FStar_Option.get  in
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
    let uu____7187 = deps.dep_graph  in
    match uu____7187 with
    | Deps deps1 ->
        let uu____7191 =
          let uu____7193 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____7211 =
                       let uu____7213 =
                         let uu____7215 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____7215
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7213
                        in
                     uu____7211 :: out) []
             in
          FStar_All.pipe_right uu____7193 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____7191 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules = FStar_Util.smap_create (Prims.of_int (41))
         in
      let should_visit lc_module_name =
        (let uu____7287 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7287) ||
          (let uu____7294 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7294)
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
            let uu____7337 =
              let uu____7341 = FStar_ST.op_Bang order  in ml_file ::
                uu____7341
               in
            FStar_ST.op_Colon_Equals order uu____7337
         in
      let rec aux uu___15_7404 =
        match uu___15_7404 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7432 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7432 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7435 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7435
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7439;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7448 = should_visit lc_module_name  in
              if uu____7448
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7456 = implementation_of deps lc_module_name  in
                  visit_file uu____7456);
                 (let uu____7461 = interface_of deps lc_module_name  in
                  visit_file uu____7461);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7473 = FStar_ST.op_Bang order  in FStar_List.rev uu____7473)
       in
    let sb =
      let uu____7504 = FStar_BigInt.of_int_fs (Prims.of_int (10000))  in
      FStar_StringBuffer.create uu____7504  in
    let pr str =
      let uu____7514 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____7514  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7567 =
          let uu____7569 =
            let uu____7573 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7573  in
          FStar_Option.get uu____7569  in
        FStar_Util.replace_chars uu____7567 46 "_"  in
      let uu____7578 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____7578  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7600 = output_file ".ml" f  in norm_path uu____7600  in
    let output_krml_file f =
      let uu____7612 = output_file ".krml" f  in norm_path uu____7612  in
    let output_cmx_file f =
      let uu____7624 = output_file ".cmx" f  in norm_path uu____7624  in
    let cache_file f =
      let uu____7636 = cache_file_name f  in norm_path uu____7636  in
    let uu____7638 =
      phase1 deps.file_system_map deps.dep_graph
        deps.interfaces_with_inlining true
       in
    match uu____7638 with
    | (widened,dep_graph) ->
        let all_checked_files =
          FStar_All.pipe_right keys
            (FStar_List.fold_left
               (fun all_checked_files  ->
                  fun file_name  ->
                    let process_one_key uu____7680 =
                      let dep_node =
                        let uu____7682 =
                          deps_try_find deps.dep_graph file_name  in
                        FStar_All.pipe_right uu____7682 FStar_Option.get  in
                      let iface_deps =
                        let uu____7692 = is_interface file_name  in
                        if uu____7692
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____7703 =
                             let uu____7707 = lowercase_module_name file_name
                                in
                             interface_of deps uu____7707  in
                           match uu____7703 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some iface ->
                               let uu____7719 =
                                 let uu____7722 =
                                   let uu____7723 =
                                     deps_try_find deps.dep_graph iface  in
                                   FStar_Option.get uu____7723  in
                                 uu____7722.edges  in
                               FStar_Pervasives_Native.Some uu____7719)
                         in
                      let iface_deps1 =
                        FStar_Util.map_opt iface_deps
                          (FStar_List.filter
                             (fun iface_dep  ->
                                let uu____7740 =
                                  FStar_Util.for_some
                                    (dep_subsumed_by iface_dep)
                                    dep_node.edges
                                   in
                                Prims.op_Negation uu____7740))
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
                            FStar_Util.remove_dups
                              (fun x  -> fun y  -> x = y)
                              (FStar_List.append files iface_files)
                         in
                      let files2 = FStar_List.map norm_path files1  in
                      let files3 =
                        FStar_List.map
                          (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                          files2
                         in
                      let files4 =
                        profile
                          (fun uu____7800  ->
                             FStar_String.concat "\\\n\t" files3)
                         in
                      let cache_file_name1 = cache_file file_name  in
                      let all_checked_files1 =
                        let uu____7808 =
                          let uu____7810 =
                            let uu____7812 = module_name_of_file file_name
                               in
                            FStar_Options.should_be_already_cached uu____7812
                             in
                          Prims.op_Negation uu____7810  in
                        if uu____7808
                        then
                          (print_entry cache_file_name1 norm_f files4;
                           cache_file_name1
                           ::
                           all_checked_files)
                        else all_checked_files  in
                      let uu____7822 =
                        let uu____7831 = FStar_Options.cmi ()  in
                        if uu____7831
                        then
                          profile
                            (fun uu____7852  ->
                               let uu____7853 = dep_graph_copy dep_graph  in
                               topological_dependences_of'
                                 deps.file_system_map uu____7853
                                 deps.interfaces_with_inlining [file_name]
                                 widened)
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
                           let uu____7890 =
                             FStar_Util.remove_dups
                               (fun x  -> fun y  -> x = y)
                               (FStar_List.append fst_files
                                  fst_files_from_iface)
                              in
                           (uu____7890, false))
                         in
                      match uu____7822 with
                      | (all_fst_files_dep,widened1) ->
                          let all_checked_fst_dep_files =
                            FStar_All.pipe_right all_fst_files_dep
                              (FStar_List.map cache_file)
                             in
                          let all_checked_fst_dep_files_string =
                            FStar_String.concat " \\\n\t"
                              all_checked_fst_dep_files
                             in
                          ((let uu____7937 = is_implementation file_name  in
                            if uu____7937
                            then
                              ((let uu____7941 =
                                  (FStar_Options.cmi ()) && widened1  in
                                if uu____7941
                                then
                                  ((let uu____7945 = output_ml_file file_name
                                       in
                                    print_entry uu____7945 cache_file_name1
                                      all_checked_fst_dep_files_string);
                                   (let uu____7947 =
                                      output_krml_file file_name  in
                                    print_entry uu____7947 cache_file_name1
                                      all_checked_fst_dep_files_string))
                                else
                                  ((let uu____7952 = output_ml_file file_name
                                       in
                                    print_entry uu____7952 cache_file_name1
                                      "");
                                   (let uu____7955 =
                                      output_krml_file file_name  in
                                    print_entry uu____7955 cache_file_name1
                                      "")));
                               (let cmx_files =
                                  let extracted_fst_files =
                                    FStar_All.pipe_right all_fst_files_dep
                                      (FStar_List.filter
                                         (fun df  ->
                                            (let uu____7980 =
                                               lowercase_module_name df  in
                                             let uu____7982 =
                                               lowercase_module_name
                                                 file_name
                                                in
                                             uu____7980 <> uu____7982) &&
                                              (let uu____7986 =
                                                 lowercase_module_name df  in
                                               FStar_Options.should_extract
                                                 uu____7986)))
                                     in
                                  FStar_All.pipe_right extracted_fst_files
                                    (FStar_List.map output_cmx_file)
                                   in
                                let uu____7996 =
                                  let uu____7998 =
                                    lowercase_module_name file_name  in
                                  FStar_Options.should_extract uu____7998  in
                                if uu____7996
                                then
                                  let cmx_files1 =
                                    FStar_String.concat "\\\n\t" cmx_files
                                     in
                                  let uu____8004 = output_cmx_file file_name
                                     in
                                  let uu____8006 = output_ml_file file_name
                                     in
                                  print_entry uu____8004 uu____8006
                                    cmx_files1
                                else ()))
                            else
                              (let uu____8012 =
                                 (let uu____8016 =
                                    let uu____8018 =
                                      lowercase_module_name file_name  in
                                    has_implementation deps.file_system_map
                                      uu____8018
                                     in
                                  Prims.op_Negation uu____8016) &&
                                   (is_interface file_name)
                                  in
                               if uu____8012
                               then
                                 let uu____8021 =
                                   (FStar_Options.cmi ()) &&
                                     (widened1 || true)
                                    in
                                 (if uu____8021
                                  then
                                    let uu____8025 =
                                      output_krml_file file_name  in
                                    print_entry uu____8025 cache_file_name1
                                      all_checked_fst_dep_files_string
                                  else
                                    (let uu____8029 =
                                       output_krml_file file_name  in
                                     print_entry uu____8029 cache_file_name1
                                       ""))
                               else ()));
                           all_checked_files1)
                       in
                    profile process_one_key) [])
           in
        let all_fst_files =
          let uu____8042 =
            FStar_All.pipe_right keys (FStar_List.filter is_implementation)
             in
          FStar_All.pipe_right uu____8042
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_fsti_files =
          let uu____8064 =
            FStar_All.pipe_right keys (FStar_List.filter is_interface)  in
          FStar_All.pipe_right uu____8064
            (FStar_Util.sort_with FStar_String.compare)
           in
        let all_ml_files =
          let ml_file_map = FStar_Util.smap_create (Prims.of_int (41))  in
          FStar_All.pipe_right all_fst_files
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8105 = FStar_Options.should_extract mname  in
                  if uu____8105
                  then
                    let uu____8108 = output_ml_file fst_file  in
                    FStar_Util.smap_add ml_file_map mname uu____8108
                  else ()));
          sort_output_files ml_file_map  in
        let all_krml_files =
          let krml_file_map = FStar_Util.smap_create (Prims.of_int (41))  in
          FStar_All.pipe_right keys
            (FStar_List.iter
               (fun fst_file  ->
                  let mname = lowercase_module_name fst_file  in
                  let uu____8135 = output_krml_file fst_file  in
                  FStar_Util.smap_add krml_file_map mname uu____8135));
          sort_output_files krml_file_map  in
        let print_all tag files =
          pr tag;
          pr "=\\\n\t";
          FStar_List.iter (fun f  -> pr (norm_path f); pr " \\\n\t") files;
          pr "\n"  in
        (print_all "ALL_FST_FILES" all_fst_files;
         print_all "ALL_FSTI_FILES" all_fsti_files;
         print_all "ALL_CHECKED_FILES" all_checked_files;
         print_all "ALL_ML_FILES" all_ml_files;
         print_all "ALL_KRML_FILES" all_krml_files;
         FStar_StringBuffer.output_channel FStar_Util.stdout sb)
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____8185 = FStar_Options.dep ()  in
    match uu____8185 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        profile (fun uu____8194  -> print_full deps)
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8199 ->
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
         fun uu____8254  ->
           fun s  ->
             match uu____8254 with
             | (v0,v1) ->
                 let uu____8283 =
                   let uu____8285 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____8285  in
                 FStar_String.op_Hat s uu____8283) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8306 =
        let uu____8308 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8308  in
      has_interface deps.file_system_map uu____8306
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8324 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8324  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8335 =
                   let uu____8337 = module_name_of_file f  in
                   FStar_String.lowercase uu____8337  in
                 uu____8335 = m)))
  