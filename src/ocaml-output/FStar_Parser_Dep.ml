open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____18 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____29 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____40 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____63 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____74 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____85 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____96 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____107 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____155 =
             (l > lext) &&
               (let uu____158 = FStar_String.substring f (l - lext) lext  in
                uu____158 = ext)
              in
           if uu____155
           then
             let uu____165 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____165
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____172 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____172 with
    | (FStar_Pervasives_Native.Some m)::uu____186 ->
        FStar_Pervasives_Native.Some m
    | uu____198 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____215 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____215 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____229 = is_interface f  in Prims.op_Negation uu____229 
let list_of_option :
  'Auu____236 .
    'Auu____236 FStar_Pervasives_Native.option -> 'Auu____236 Prims.list
  =
  fun uu___0_245  ->
    match uu___0_245 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____254 .
    ('Auu____254 FStar_Pervasives_Native.option * 'Auu____254
      FStar_Pervasives_Native.option) -> 'Auu____254 Prims.list
  =
  fun uu____269  ->
    match uu____269 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____297 =
      let uu____301 = FStar_Util.basename f  in
      check_and_strip_suffix uu____301  in
    match uu____297 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____308 =
          let uu____314 = FStar_Util.format1 "not a valid FStar file: %s" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____314)  in
        FStar_Errors.raise_err uu____308
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____328 = module_name_of_file f  in
    FStar_String.lowercase uu____328
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____341 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____341 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____344 ->
        let uu____347 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____347
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____387 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____410 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____433 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | FriendImplementation _0 -> true
    | uu____456 -> false
  
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | FriendImplementation _0 -> _0 
let (dep_to_string : dependence -> Prims.string) =
  fun uu___1_474  ->
    match uu___1_474 with
    | UseInterface f -> FStar_String.op_Hat "UseInterface " f
    | PreferInterface f -> FStar_String.op_Hat "PreferInterface " f
    | UseImplementation f -> FStar_String.op_Hat "UseImplementation " f
    | FriendImplementation f -> FStar_String.op_Hat "FriendImplementation " f
  
type dependences = dependence Prims.list
let empty_dependences : 'Auu____493 . unit -> 'Auu____493 Prims.list =
  fun uu____496  -> [] 
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
    match projectee with | P_begin_module _0 -> true | uu____609 -> false
  
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_begin_module _0 -> _0 
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_open _0 -> true | uu____633 -> false
  
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_open _0 -> _0 
let (uu___is_P_open_module_or_namespace : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_open_module_or_namespace _0 -> true
    | uu____671 -> false
  
let (__proj__P_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStar_Ident.lid)) =
  fun projectee  ->
    match projectee with | P_open_module_or_namespace _0 -> _0
  
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_dep _0 -> true | uu____707 -> false
  
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_dep _0 -> _0 
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_alias _0 -> true | uu____745 -> false
  
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStar_Ident.ident * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | P_alias _0 -> _0 
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | P_lid _0 -> true | uu____776 -> false
  
let (__proj__P_lid__item___0 : parsing_data_elt -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | P_lid _0 -> _0 
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | P_inline_for_extraction  -> true
    | uu____794 -> false
  
type parsing_data =
  | Mk_pd of parsing_data_elt Prims.list 
let (uu___is_Mk_pd : parsing_data -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk_pd__item___0 : parsing_data -> parsing_data_elt Prims.list) =
  fun projectee  -> match projectee with | Mk_pd _0 -> _0 
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt  ->
    let str_of_open_kind uu___2_837 =
      match uu___2_837 with
      | Open_module  -> "P_open_module"
      | Open_namespace  -> "P_open_namespace"  in
    match elt with
    | P_begin_module lid ->
        let uu____843 =
          let uu____845 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____845 ")"  in
        FStar_String.op_Hat "P_begin_module (" uu____843
    | P_open (b,lid) ->
        let uu____853 =
          let uu____855 = FStar_Util.string_of_bool b  in
          let uu____857 =
            let uu____859 =
              let uu____861 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____861 ")"  in
            FStar_String.op_Hat ", " uu____859  in
          FStar_String.op_Hat uu____855 uu____857  in
        FStar_String.op_Hat "P_open (" uu____853
    | P_open_module_or_namespace (k,lid) ->
        let uu____868 =
          let uu____870 =
            let uu____872 =
              let uu____874 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____874 ")"  in
            FStar_String.op_Hat ", " uu____872  in
          FStar_String.op_Hat (str_of_open_kind k) uu____870  in
        FStar_String.op_Hat "P_open_module_or_namespace (" uu____868
    | P_dep (b,lid) ->
        let uu____883 =
          let uu____885 = FStar_Ident.text_of_lid lid  in
          let uu____887 =
            let uu____889 =
              let uu____891 = FStar_Util.string_of_bool b  in
              FStar_String.op_Hat uu____891 ")"  in
            FStar_String.op_Hat ", " uu____889  in
          FStar_String.op_Hat uu____885 uu____887  in
        FStar_String.op_Hat "P_dep (" uu____883
    | P_alias (id1,lid) ->
        let uu____898 =
          let uu____900 = FStar_Ident.text_of_id id1  in
          let uu____902 =
            let uu____904 =
              let uu____906 = FStar_Ident.text_of_lid lid  in
              FStar_String.op_Hat uu____906 ")"  in
            FStar_String.op_Hat ", " uu____904  in
          FStar_String.op_Hat uu____900 uu____902  in
        FStar_String.op_Hat "P_alias (" uu____898
    | P_lid lid ->
        let uu____912 =
          let uu____914 = FStar_Ident.text_of_lid lid  in
          FStar_String.op_Hat uu____914 ")"  in
        FStar_String.op_Hat "P_lid (" uu____912
    | P_inline_for_extraction  -> "P_inline_for_extraction"
  
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun uu___3_925  ->
    match uu___3_925 with
    | Mk_pd l ->
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun s  ->
                fun elt  ->
                  let uu____940 =
                    let uu____942 =
                      FStar_All.pipe_right elt str_of_parsing_data_elt  in
                    FStar_String.op_Hat "; " uu____942  in
                  FStar_String.op_Hat s uu____940) "")
  
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
          (let uu____992 = FStar_Ident.text_of_id i1  in
           let uu____994 = FStar_Ident.text_of_id i2  in
           uu____992 = uu____994) && (FStar_Ident.lid_equals l1 l2)
      | (P_lid l1,P_lid l2) -> FStar_Ident.lid_equals l1 l2
      | (P_inline_for_extraction ,P_inline_for_extraction ) -> true
      | (uu____1000,uu____1001) -> false
  
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
  fun uu____1217  ->
    fun k  -> match uu____1217 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu____1239  ->
    fun k  ->
      fun v1  -> match uu____1239 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____1254  -> match uu____1254 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____1266  ->
    let uu____1267 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____1267
  
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
  let uu____1325 = deps_empty ()  in
  let uu____1326 = FStar_Util.smap_create (Prims.parse_int "0")  in
  let uu____1338 = FStar_Util.smap_create (Prims.parse_int "0")  in
  mk_deps uu____1325 uu____1326 [] [] [] uu____1338 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___4_1351  ->
    match uu___4_1351 with
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
      let uu____1380 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1380 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____1407) ->
          let uu____1429 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1429
      | FStar_Pervasives_Native.Some
          (uu____1432,FStar_Pervasives_Native.Some fn) ->
          let uu____1455 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____1455
      | uu____1458 -> FStar_Pervasives_Native.None
  
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1491 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1491 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____1518) ->
          FStar_Pervasives_Native.Some iface
      | uu____1541 -> FStar_Pervasives_Native.None
  
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1574 = FStar_Util.smap_try_find file_system_map key  in
      match uu____1574 with
      | FStar_Pervasives_Native.Some
          (uu____1600,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____1624 -> FStar_Pervasives_Native.None
  
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
      let uu____1685 = interface_of_internal file_system_map key  in
      FStar_Option.isSome uu____1685
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____1705 = implementation_of_internal file_system_map key  in
      FStar_Option.isSome uu____1705
  
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let lax1 = FStar_Options.lax ()  in
    let cache_fn =
      if lax1
      then FStar_String.op_Hat fn ".checked.lax"
      else FStar_String.op_Hat fn ".checked"  in
    let mname = FStar_All.pipe_right fn module_name_of_file  in
    let uu____1740 =
      let uu____1744 = FStar_All.pipe_right cache_fn FStar_Util.basename  in
      FStar_Options.find_file uu____1744  in
    match uu____1740 with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStar_Options.prepend_cache_dir cache_fn
           in
        ((let uu____1755 =
            ((let uu____1759 = FStar_Options.dep ()  in
              FStar_Option.isSome uu____1759) &&
               (let uu____1765 = FStar_Options.should_be_already_cached mname
                   in
                Prims.op_Negation uu____1765))
              &&
              ((Prims.op_Negation
                  (FStar_Util.file_exists expected_cache_file))
                 ||
                 (let uu____1768 =
                    FStar_Util.paths_to_same_file path expected_cache_file
                     in
                  Prims.op_Negation uu____1768))
             in
          if uu____1755
          then
            let uu____1771 =
              let uu____1777 =
                let uu____1779 = FStar_Options.prepend_cache_dir cache_fn  in
                FStar_Util.format3
                  "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s"
                  mname path uu____1779
                 in
              (FStar_Errors.Warning_UnexpectedCheckedFile, uu____1777)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1771
          else ());
         path)
    | FStar_Pervasives_Native.None  ->
        let uu____1786 =
          FStar_All.pipe_right mname FStar_Options.should_be_already_cached
           in
        if uu____1786
        then
          let uu____1792 =
            let uu____1798 =
              FStar_Util.format1
                "Expected %s to be already checked but could not find it"
                mname
               in
            (FStar_Errors.Error_AlreadyCachedAssertionFailure, uu____1798)
             in
          FStar_Errors.raise_err uu____1792
        else FStar_Options.prepend_cache_dir cache_fn
     in
  let memo = FStar_Util.smap_create (Prims.parse_int "100")  in
  let memo1 f x =
    let uu____1834 = FStar_Util.smap_try_find memo x  in
    match uu____1834 with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None  ->
        let res = f x  in (FStar_Util.smap_add memo x res; res)
     in
  memo1 checked_file_and_exists_flag 
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps  ->
    fun fn  ->
      let uu____1861 = FStar_Util.smap_try_find deps.parse_results fn  in
      FStar_All.pipe_right uu____1861 FStar_Util.must
  
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
                      (let uu____1915 = lowercase_module_name fn  in
                       key = uu____1915)))
             in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____1934 = interface_of_internal file_system_map key  in
              (match uu____1934 with
               | FStar_Pervasives_Native.None  ->
                   let uu____1941 =
                     let uu____1947 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____1947)  in
                   FStar_Errors.raise_err uu____1941
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____1957 =
                (cmd_line_has_impl key) &&
                  (let uu____1960 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____1960)
                 in
              if uu____1957
              then
                let uu____1967 = FStar_Options.expose_interfaces ()  in
                (if uu____1967
                 then
                   let uu____1971 =
                     let uu____1973 =
                       implementation_of_internal file_system_map key  in
                     FStar_Option.get uu____1973  in
                   maybe_use_cache_of uu____1971
                 else
                   (let uu____1980 =
                      let uu____1986 =
                        let uu____1988 =
                          let uu____1990 =
                            implementation_of_internal file_system_map key
                             in
                          FStar_Option.get uu____1990  in
                        let uu____1995 =
                          let uu____1997 =
                            interface_of_internal file_system_map key  in
                          FStar_Option.get uu____1997  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____1988 uu____1995
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____1986)
                       in
                    FStar_Errors.raise_err uu____1980))
              else
                (let uu____2007 =
                   let uu____2009 = interface_of_internal file_system_map key
                      in
                   FStar_Option.get uu____2009  in
                 maybe_use_cache_of uu____2007)
          | PreferInterface key ->
              let uu____2016 = implementation_of_internal file_system_map key
                 in
              (match uu____2016 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2022 =
                     let uu____2028 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2028)
                      in
                   FStar_Errors.raise_err uu____2022
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu____2038 = implementation_of_internal file_system_map key
                 in
              (match uu____2038 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2044 =
                     let uu____2050 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2050)
                      in
                   FStar_Errors.raise_err uu____2044
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu____2060 = implementation_of_internal file_system_map key
                 in
              (match uu____2060 with
               | FStar_Pervasives_Native.None  ->
                   let uu____2066 =
                     let uu____2072 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____2072)
                      in
                   FStar_Errors.raise_err uu____2066
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
          let uu____2133 = deps_try_find deps fn  in
          match uu____2133 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some
              { edges = deps1; color = uu____2141;_} ->
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
    (let uu____2155 =
       let uu____2157 =
         let uu____2159 =
           let uu____2161 =
             let uu____2165 =
               let uu____2169 = deps_keys graph  in
               FStar_List.unique uu____2169  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____2183 =
                      let uu____2184 = deps_try_find graph k  in
                      FStar_Util.must uu____2184  in
                    uu____2183.edges  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    let uu____2205 =
                      let uu____2207 = lowercase_module_name k  in
                      r uu____2207  in
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2205
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____2165
              in
           FStar_String.concat "\n" uu____2161  in
         FStar_String.op_Hat uu____2159 "\n}\n"  in
       FStar_String.op_Hat "digraph {\n" uu____2157  in
     FStar_Util.write_file "dep.graph" uu____2155)
  
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____2228  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____2254 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____2254  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.is_directory d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____2294 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____2294
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____2331 =
              let uu____2337 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____2337)  in
            FStar_Errors.raise_err uu____2331)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____2400 = FStar_Util.smap_try_find map1 key  in
      match uu____2400 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____2447 = is_interface full_path  in
          if uu____2447
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____2496 = is_interface full_path  in
          if uu____2496
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____2538 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____2556  ->
          match uu____2556 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____2538);
    FStar_List.iter
      (fun f  ->
         let uu____2575 = lowercase_module_name f  in add_entry uu____2575 f)
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
        (let uu____2607 =
           let uu____2611 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____2611  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____2647 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____2647  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____2607);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____2767 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____2767 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____2790 = string_of_lid l last1  in
      FStar_String.lowercase uu____2790
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____2799 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____2799
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____2821 =
        let uu____2823 =
          let uu____2825 =
            let uu____2827 =
              let uu____2831 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____2831  in
            FStar_Util.must uu____2827  in
          FStar_String.lowercase uu____2825  in
        uu____2823 <> k'  in
      if uu____2821
      then
        let uu____2836 = FStar_Ident.range_of_lid lid  in
        let uu____2837 =
          let uu____2843 =
            let uu____2845 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____2845 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____2843)  in
        FStar_Errors.log_issue uu____2836 uu____2837
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2861 -> false
  
let (hard_coded_dependencies :
  Prims.string -> (FStar_Ident.lident * open_kind) Prims.list) =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____2883 = FStar_Options.prims_basename ()  in
      let uu____2885 =
        let uu____2889 = FStar_Options.pervasives_basename ()  in
        let uu____2891 =
          let uu____2895 = FStar_Options.pervasives_native_basename ()  in
          [uu____2895]  in
        uu____2889 :: uu____2891  in
      uu____2883 :: uu____2885  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____2938 =
         let uu____2941 = lowercase_module_name full_filename  in
         namespace_of_module uu____2941  in
       match uu____2938 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d  ->
    fun d'  ->
      match (d, d') with
      | (PreferInterface l',FriendImplementation l) -> l = l'
      | uu____2980 -> d = d'
  
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
            let uu____3098 =
              (is_interface filename1) &&
                (has_implementation original_map1 mname)
               in
            if uu____3098 then [UseImplementation mname] else []  in
          let auto_open =
            let uu____3108 = hard_coded_dependencies filename1  in
            FStar_All.pipe_right uu____3108
              (FStar_List.map
                 (fun uu____3130  ->
                    match uu____3130 with
                    | (lid,k) -> P_open_module_or_namespace (k, lid)))
             in
          let working_map = FStar_Util.smap_copy original_map1  in
          let set_interface_inlining uu____3165 =
            let uu____3166 = is_interface filename1  in
            if uu____3166
            then FStar_ST.op_Colon_Equals has_inline_for_extraction true
            else ()  in
          let add_dep deps1 d =
            let uu____3288 =
              let uu____3290 =
                let uu____3292 = FStar_ST.op_Bang deps1  in
                FStar_List.existsML (dep_subsumed_by d) uu____3292  in
              Prims.op_Negation uu____3290  in
            if uu____3288
            then
              let uu____3319 =
                let uu____3322 = FStar_ST.op_Bang deps1  in d :: uu____3322
                 in
              FStar_ST.op_Colon_Equals deps1 uu____3319
            else ()  in
          let dep_edge module_name is_friend =
            if is_friend
            then FriendImplementation module_name
            else PreferInterface module_name  in
          let add_dependence_edge original_or_working_map lid is_friend =
            let key = lowercase_join_longident lid true  in
            let uu____3413 = resolve_module_name original_or_working_map key
               in
            match uu____3413 with
            | FStar_Pervasives_Native.Some module_name ->
                (add_dep deps (dep_edge module_name is_friend); true)
            | uu____3423 -> false  in
          let record_open_module let_open lid =
            let uu____3442 =
              (let_open && (add_dependence_edge working_map lid false)) ||
                ((Prims.op_Negation let_open) &&
                   (add_dependence_edge original_map1 lid false))
               in
            if uu____3442
            then true
            else
              (if let_open
               then
                 (let uu____3453 = FStar_Ident.range_of_lid lid  in
                  let uu____3454 =
                    let uu____3460 =
                      let uu____3462 = string_of_lid lid true  in
                      FStar_Util.format1 "Module not found: %s" uu____3462
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3460)
                     in
                  FStar_Errors.log_issue uu____3453 uu____3454)
               else ();
               false)
             in
          let record_open_namespace lid =
            let key = lowercase_join_longident lid true  in
            let r = enter_namespace original_map1 working_map key  in
            if Prims.op_Negation r
            then
              let uu____3482 = FStar_Ident.range_of_lid lid  in
              let uu____3483 =
                let uu____3489 =
                  let uu____3491 = string_of_lid lid true  in
                  FStar_Util.format1
                    "No modules in namespace %s and no file with that name either"
                    uu____3491
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____3489)
                 in
              FStar_Errors.log_issue uu____3482 uu____3483
            else ()  in
          let record_open let_open lid =
            let uu____3511 = record_open_module let_open lid  in
            if uu____3511
            then ()
            else
              if Prims.op_Negation let_open
              then record_open_namespace lid
              else ()
             in
          let record_open_module_or_namespace uu____3528 =
            match uu____3528 with
            | (lid,kind) ->
                (match kind with
                 | Open_namespace  -> record_open_namespace lid
                 | Open_module  ->
                     let uu____3535 = record_open_module false lid  in ())
             in
          let record_module_alias ident lid =
            let key =
              let uu____3552 = FStar_Ident.text_of_id ident  in
              FStar_String.lowercase uu____3552  in
            let alias = lowercase_join_longident lid true  in
            let uu____3557 = FStar_Util.smap_try_find original_map1 alias  in
            match uu____3557 with
            | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                (FStar_Util.smap_add working_map key deps_of_aliased_module;
                 (let uu____3614 =
                    let uu____3615 = lowercase_join_longident lid true  in
                    dep_edge uu____3615 false  in
                  add_dep deps uu____3614);
                 true)
            | FStar_Pervasives_Native.None  ->
                ((let uu____3631 = FStar_Ident.range_of_lid lid  in
                  let uu____3632 =
                    let uu____3638 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias
                       in
                    (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                      uu____3638)
                     in
                  FStar_Errors.log_issue uu____3631 uu____3632);
                 false)
             in
          let add_dep_on_module module_name is_friend =
            let uu____3656 =
              add_dependence_edge working_map module_name is_friend  in
            if uu____3656
            then ()
            else
              (let uu____3661 = FStar_Options.debug_any ()  in
               if uu____3661
               then
                 let uu____3664 = FStar_Ident.range_of_lid module_name  in
                 let uu____3665 =
                   let uu____3671 =
                     let uu____3673 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____3673
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____3671)
                    in
                 FStar_Errors.log_issue uu____3664 uu____3665
               else ())
             in
          let record_lid lid =
            match lid.FStar_Ident.ns with
            | [] -> ()
            | uu____3685 ->
                let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns
                   in
                add_dep_on_module module_name false
             in
          let begin_module lid =
            if (FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")
            then
              let uu____3698 =
                let uu____3700 = namespace_of_lid lid  in
                enter_namespace original_map1 working_map uu____3700  in
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
                           let uu____3726 = record_module_alias id1 lid  in
                           ()
                       | P_lid lid -> record_lid lid
                       | P_inline_for_extraction  ->
                           set_interface_inlining ())));
          (let uu____3729 = FStar_ST.op_Bang deps  in
           let uu____3755 = FStar_ST.op_Bang has_inline_for_extraction  in
           (uu____3729, uu____3755, mo_roots))
           in
        let data_from_cache =
          FStar_All.pipe_right filename get_parsing_data_from_cache  in
        let uu____3789 =
          FStar_All.pipe_right data_from_cache FStar_Util.is_some  in
        if uu____3789
        then
          let uu____3808 =
            let uu____3820 =
              FStar_All.pipe_right data_from_cache FStar_Util.must  in
            from_parsing_data uu____3820 original_map filename  in
          match uu____3808 with
          | (deps,has_inline_for_extraction,mo_roots) ->
              let uu____3849 =
                FStar_All.pipe_right data_from_cache FStar_Util.must  in
              (uu____3849, deps, has_inline_for_extraction, mo_roots)
        else
          (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")
              in
           let pd = FStar_Util.mk_ref []  in
           let add_to_parsing_data elt =
             let uu____3878 =
               let uu____3880 =
                 let uu____3882 = FStar_ST.op_Bang pd  in
                 FStar_List.existsML (fun e  -> parsing_data_elt_eq e elt)
                   uu____3882
                  in
               Prims.op_Negation uu____3880  in
             if uu____3878
             then
               let uu____3911 =
                 let uu____3914 = FStar_ST.op_Bang pd  in elt :: uu____3914
                  in
               FStar_ST.op_Colon_Equals pd uu____3911
             else ()  in
           let rec collect_module uu___5_4071 =
             match uu___5_4071 with
             | FStar_Parser_AST.Module (lid,decls) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
                  collect_decls decls)
             | FStar_Parser_AST.Interface (lid,decls,uu____4082) ->
                 (check_module_declaration_against_filename lid filename;
                  add_to_parsing_data (P_begin_module lid);
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
                  then add_to_parsing_data P_inline_for_extraction
                  else ()) decls
           
           and collect_decl d =
             match d with
             | FStar_Parser_AST.Include lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Open lid ->
                 add_to_parsing_data (P_open (false, lid))
             | FStar_Parser_AST.Friend lid ->
                 let uu____4111 =
                   let uu____4112 =
                     let uu____4118 =
                       let uu____4119 = lowercase_join_longident lid true  in
                       FStar_All.pipe_right uu____4119 FStar_Ident.lid_of_str
                        in
                     (true, uu____4118)  in
                   P_dep uu____4112  in
                 add_to_parsing_data uu____4111
             | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStar_Parser_AST.TopLevelLet (uu____4127,patterms) ->
                 FStar_List.iter
                   (fun uu____4149  ->
                      match uu____4149 with
                      | (pat,t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStar_Parser_AST.Main t -> collect_term t
             | FStar_Parser_AST.Splice (uu____4158,t) -> collect_term t
             | FStar_Parser_AST.Assume (uu____4164,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4166;
                   FStar_Parser_AST.mdest = uu____4167;
                   FStar_Parser_AST.lift_op =
                     FStar_Parser_AST.NonReifiableLift t;_}
                 -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4169;
                   FStar_Parser_AST.mdest = uu____4170;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
                 -> collect_term t
             | FStar_Parser_AST.Val (uu____4172,t) -> collect_term t
             | FStar_Parser_AST.SubEffect
                 { FStar_Parser_AST.msource = uu____4174;
                   FStar_Parser_AST.mdest = uu____4175;
                   FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                     (t0,t1);_}
                 -> (collect_term t0; collect_term t1)
             | FStar_Parser_AST.Tycon (uu____4179,tc,ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStar_Parser_Const.mk_class_lid)
                  else ();
                  (let ts1 =
                     FStar_List.map
                       (fun uu____4218  ->
                          match uu____4218 with | (x,docnik) -> x) ts
                      in
                   FStar_List.iter collect_tycon ts1))
             | FStar_Parser_AST.Exception (uu____4231,t) ->
                 FStar_Util.iter_opt t collect_term
             | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStar_Parser_AST.Fsdoc uu____4238 -> ()
             | FStar_Parser_AST.Pragma uu____4239 -> ()
             | FStar_Parser_AST.TopLevelModule lid ->
                 (FStar_Util.incr num_of_toplevelmods;
                  (let uu____4242 =
                     let uu____4244 = FStar_ST.op_Bang num_of_toplevelmods
                        in
                     uu____4244 > (Prims.parse_int "1")  in
                   if uu____4242
                   then
                     let uu____4269 =
                       let uu____4275 =
                         let uu____4277 = string_of_lid lid true  in
                         FStar_Util.format1
                           "Automatic dependency analysis demands one module per file (module %s not supported)"
                           uu____4277
                          in
                       (FStar_Errors.Fatal_OneModulePerFile, uu____4275)  in
                     let uu____4282 = FStar_Ident.range_of_lid lid  in
                     FStar_Errors.raise_error uu____4269 uu____4282
                   else ()))
           
           and collect_tycon uu___6_4285 =
             match uu___6_4285 with
             | FStar_Parser_AST.TyconAbstract (uu____4286,binders,k) ->
                 (collect_binders binders; FStar_Util.iter_opt k collect_term)
             | FStar_Parser_AST.TyconAbbrev (uu____4298,binders,k,t) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  collect_term t)
             | FStar_Parser_AST.TyconRecord (uu____4312,binders,k,identterms)
                 ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4358  ->
                       match uu____4358 with
                       | (uu____4367,t,uu____4369) -> collect_term t)
                    identterms)
             | FStar_Parser_AST.TyconVariant
                 (uu____4374,binders,k,identterms) ->
                 (collect_binders binders;
                  FStar_Util.iter_opt k collect_term;
                  FStar_List.iter
                    (fun uu____4436  ->
                       match uu____4436 with
                       | (uu____4450,t,uu____4452,uu____4453) ->
                           FStar_Util.iter_opt t collect_term) identterms)
           
           and collect_effect_decl uu___7_4464 =
             match uu___7_4464 with
             | FStar_Parser_AST.DefineEffect (uu____4465,binders,t,decls) ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStar_Parser_AST.RedefineEffect (uu____4479,binders,t) ->
                 (collect_binders binders; collect_term t)
           
           and collect_binders binders =
             FStar_List.iter collect_binder binders
           
           and collect_binder b =
             collect_aqual b.FStar_Parser_AST.aqual;
             (match b with
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                    (uu____4492,t);
                  FStar_Parser_AST.brange = uu____4494;
                  FStar_Parser_AST.blevel = uu____4495;
                  FStar_Parser_AST.aqual = uu____4496;_} -> collect_term t
              | {
                  FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                    (uu____4499,t);
                  FStar_Parser_AST.brange = uu____4501;
                  FStar_Parser_AST.blevel = uu____4502;
                  FStar_Parser_AST.aqual = uu____4503;_} -> collect_term t
              | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                  FStar_Parser_AST.brange = uu____4507;
                  FStar_Parser_AST.blevel = uu____4508;
                  FStar_Parser_AST.aqual = uu____4509;_} -> collect_term t
              | uu____4512 -> ())
           
           and collect_aqual uu___8_4513 =
             match uu___8_4513 with
             | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
                 collect_term t
             | uu____4517 -> ()
           
           and collect_term t = collect_term' t.FStar_Parser_AST.tm
           
           and collect_constant uu___9_4521 =
             match uu___9_4521 with
             | FStar_Const.Const_int
                 (uu____4522,FStar_Pervasives_Native.Some (signedness,width))
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
                 let uu____4549 =
                   let uu____4550 =
                     let uu____4556 =
                       let uu____4557 =
                         FStar_Util.format2 "fstar.%sint%s" u w  in
                       FStar_All.pipe_right uu____4557 FStar_Ident.lid_of_str
                        in
                     (false, uu____4556)  in
                   P_dep uu____4550  in
                 add_to_parsing_data uu____4549
             | FStar_Const.Const_char uu____4563 ->
                 let uu____4565 =
                   let uu____4566 =
                     let uu____4572 =
                       FStar_All.pipe_right "fstar.char"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4572)  in
                   P_dep uu____4566  in
                 add_to_parsing_data uu____4565
             | FStar_Const.Const_float uu____4577 ->
                 let uu____4578 =
                   let uu____4579 =
                     let uu____4585 =
                       FStar_All.pipe_right "fstar.float"
                         FStar_Ident.lid_of_str
                        in
                     (false, uu____4585)  in
                   P_dep uu____4579  in
                 add_to_parsing_data uu____4578
             | uu____4590 -> ()
           
           and collect_term' uu___12_4591 =
             match uu___12_4591 with
             | FStar_Parser_AST.Wild  -> ()
             | FStar_Parser_AST.Const c -> collect_constant c
             | FStar_Parser_AST.Op (s,ts) ->
                 ((let uu____4600 =
                     let uu____4602 = FStar_Ident.text_of_id s  in
                     uu____4602 = "@"  in
                   if uu____4600
                   then
                     let uu____4607 =
                       let uu____4608 =
                         let uu____4609 =
                           FStar_Ident.path_of_text
                             "FStar.List.Tot.Base.append"
                            in
                         FStar_Ident.lid_of_path uu____4609
                           FStar_Range.dummyRange
                          in
                       FStar_Parser_AST.Name uu____4608  in
                     collect_term' uu____4607
                   else ());
                  FStar_List.iter collect_term ts)
             | FStar_Parser_AST.Tvar uu____4613 -> ()
             | FStar_Parser_AST.Uvar uu____4614 -> ()
             | FStar_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Projector (lid,uu____4617) ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStar_Parser_AST.Construct (lid,termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStar_List.iter
                    (fun uu____4642  ->
                       match uu____4642 with
                       | (t,uu____4648) -> collect_term t) termimps)
             | FStar_Parser_AST.Abs (pats,t) ->
                 (collect_patterns pats; collect_term t)
             | FStar_Parser_AST.App (t1,t2,uu____4658) ->
                 (collect_term t1; collect_term t2)
             | FStar_Parser_AST.Let (uu____4660,patterms,t) ->
                 (FStar_List.iter
                    (fun uu____4710  ->
                       match uu____4710 with
                       | (attrs_opt,(pat,t1)) ->
                           ((let uu____4739 =
                               FStar_Util.map_opt attrs_opt
                                 (FStar_List.iter collect_term)
                                in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStar_Parser_AST.LetOpen (lid,t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStar_Parser_AST.Bind (uu____4750,t1,t2) ->
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
                    (fun uu____4846  ->
                       match uu____4846 with
                       | (uu____4851,t1) -> collect_term t1) idterms)
             | FStar_Parser_AST.Project (t,uu____4854) -> collect_term t
             | FStar_Parser_AST.Product (binders,t) ->
                 (collect_binders binders; collect_term t)
             | FStar_Parser_AST.Sum (binders,t) ->
                 (FStar_List.iter
                    (fun uu___10_4883  ->
                       match uu___10_4883 with
                       | FStar_Util.Inl b -> collect_binder b
                       | FStar_Util.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStar_Parser_AST.QForall (binders,(uu____4891,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.QExists (binders,(uu____4925,ts),t) ->
                 (collect_binders binders;
                  FStar_List.iter (FStar_List.iter collect_term) ts;
                  collect_term t)
             | FStar_Parser_AST.Refine (binder,t) ->
                 (collect_binder binder; collect_term t)
             | FStar_Parser_AST.NamedTyp (uu____4961,t) -> collect_term t
             | FStar_Parser_AST.Paren t -> collect_term t
             | FStar_Parser_AST.Requires (t,uu____4965) -> collect_term t
             | FStar_Parser_AST.Ensures (t,uu____4973) -> collect_term t
             | FStar_Parser_AST.Labeled (t,uu____4981,uu____4982) ->
                 collect_term t
             | FStar_Parser_AST.Quote (t,uu____4988) -> collect_term t
             | FStar_Parser_AST.Antiquote t -> collect_term t
             | FStar_Parser_AST.VQuote t -> collect_term t
             | FStar_Parser_AST.Attributes cattributes ->
                 FStar_List.iter collect_term cattributes
             | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
                 ((let uu____5002 =
                     let uu____5003 =
                       let uu____5009 = FStar_Ident.lid_of_str "FStar.Calc"
                          in
                       (false, uu____5009)  in
                     P_dep uu____5003  in
                   add_to_parsing_data uu____5002);
                  collect_term rel;
                  collect_term init1;
                  FStar_List.iter
                    (fun uu___11_5021  ->
                       match uu___11_5021 with
                       | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
           
           and collect_patterns ps = FStar_List.iter collect_pattern ps
           
           and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
           
           and collect_pattern' uu___13_5031 =
             match uu___13_5031 with
             | FStar_Parser_AST.PatVar (uu____5032,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatTvar (uu____5038,aqual) ->
                 collect_aqual aqual
             | FStar_Parser_AST.PatWild aqual -> collect_aqual aqual
             | FStar_Parser_AST.PatOp uu____5047 -> ()
             | FStar_Parser_AST.PatConst uu____5048 -> ()
             | FStar_Parser_AST.PatApp (p,ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStar_Parser_AST.PatName uu____5056 -> ()
             | FStar_Parser_AST.PatList ps -> collect_patterns ps
             | FStar_Parser_AST.PatOr ps -> collect_patterns ps
             | FStar_Parser_AST.PatTuple (ps,uu____5064) ->
                 collect_patterns ps
             | FStar_Parser_AST.PatRecord lidpats ->
                 FStar_List.iter
                   (fun uu____5085  ->
                      match uu____5085 with
                      | (uu____5090,p) -> collect_pattern p) lidpats
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.None )) ->
                 (collect_pattern p; collect_term t)
             | FStar_Parser_AST.PatAscribed
                 (p,(t,FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           
           and collect_branches bs = FStar_List.iter collect_branch bs
           
           and collect_branch uu____5135 =
             match uu____5135 with
             | (pat,t1,t2) ->
                 (collect_pattern pat;
                  FStar_Util.iter_opt t1 collect_term;
                  collect_term t2)
            in
           let uu____5153 = FStar_Parser_Driver.parse_file filename  in
           match uu____5153 with
           | (ast,uu____5179) ->
               (collect_module ast;
                (let pd1 =
                   let uu____5196 =
                     let uu____5199 = FStar_ST.op_Bang pd  in
                     FStar_List.rev uu____5199  in
                   Mk_pd uu____5196  in
                 let uu____5225 = from_parsing_data pd1 original_map filename
                    in
                 match uu____5225 with
                 | (deps,has_inline_for_extraction,mo_roots) ->
                     (pd1, deps, has_inline_for_extraction, mo_roots))))
  
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap FStar_ST.ref)
  =
  let uu____5284 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____5284 
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool)
    FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph  ->
    let uu____5406 = dep_graph  in
    match uu____5406 with
    | Deps g -> let uu____5410 = FStar_Util.smap_copy g  in Deps uu____5410
  
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
            let rec all_friend_deps_1 dep_graph1 cycle uu____5555 filename =
              match uu____5555 with
              | (all_friends,all_files) ->
                  let dep_node =
                    let uu____5596 = deps_try_find dep_graph1 filename  in
                    FStar_Util.must uu____5596  in
                  (match dep_node.color with
                   | Gray  ->
                       failwith
                         "Impossible: cycle detected after cycle detection has passed"
                   | Black  -> (all_friends, all_files)
                   | White  ->
                       ((let uu____5627 = FStar_Options.debug_any ()  in
                         if uu____5627
                         then
                           let uu____5630 =
                             let uu____5632 =
                               FStar_List.map dep_to_string dep_node.edges
                                in
                             FStar_String.concat ", " uu____5632  in
                           FStar_Util.print2
                             "Visiting %s: direct deps are %s\n" filename
                             uu____5630
                         else ());
                        deps_add_dep dep_graph1 filename
                          (let uu___978_5643 = dep_node  in
                           { edges = (uu___978_5643.edges); color = Gray });
                        (let uu____5644 =
                           let uu____5655 =
                             dependences_of file_system_map dep_graph1
                               root_files filename
                              in
                           all_friend_deps dep_graph1 cycle
                             (all_friends, all_files) uu____5655
                            in
                         match uu____5644 with
                         | (all_friends1,all_files1) ->
                             (deps_add_dep dep_graph1 filename
                                (let uu___984_5691 = dep_node  in
                                 {
                                   edges = (uu___984_5691.edges);
                                   color = Black
                                 });
                              (let uu____5693 = FStar_Options.debug_any ()
                                  in
                               if uu____5693
                               then FStar_Util.print1 "Adding %s\n" filename
                               else ());
                              (let uu____5699 =
                                 let uu____5703 =
                                   FStar_List.collect
                                     (fun uu___14_5710  ->
                                        match uu___14_5710 with
                                        | FriendImplementation m -> [m]
                                        | d -> []) dep_node.edges
                                    in
                                 FStar_List.append uu____5703 all_friends1
                                  in
                               (uu____5699, (filename :: all_files1)))))))
            
            and all_friend_deps dep_graph1 cycle all_friends filenames =
              FStar_List.fold_left
                (fun all_friends1  ->
                   fun k  ->
                     all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
                all_friends filenames
             in
            (let uu____5776 = FStar_Options.debug_any ()  in
             if uu____5776
             then
               FStar_Util.print_string
                 "==============Phase1==================\n"
             else ());
            (let widened = FStar_Util.mk_ref false  in
             let widen_deps friends deps =
               let uu____5805 = deps  in
               match uu____5805 with
               | Deps dg ->
                   let uu____5809 = deps_empty ()  in
                   (match uu____5809 with
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
                                  | uu____5859 -> d))
                           in
                        (FStar_Util.smap_fold dg
                           (fun filename  ->
                              fun dep_node  ->
                                fun uu____5867  ->
                                  let uu____5869 =
                                    let uu___1019_5870 = dep_node  in
                                    let uu____5871 = widen_one dep_node.edges
                                       in
                                    { edges = uu____5871; color = White }  in
                                  FStar_Util.smap_add dg' filename uu____5869)
                           ();
                         Deps dg'))
                in
             let dep_graph1 =
               let uu____5873 = (FStar_Options.cmi ()) && for_extraction  in
               if uu____5873
               then widen_deps interfaces_needing_inlining dep_graph
               else dep_graph  in
             let uu____5878 =
               all_friend_deps dep_graph1 [] ([], []) root_files  in
             match uu____5878 with
             | (friends,all_files_0) ->
                 ((let uu____5921 = FStar_Options.debug_any ()  in
                   if uu____5921
                   then
                     let uu____5924 =
                       let uu____5926 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           friends
                          in
                       FStar_String.concat ", " uu____5926  in
                     FStar_Util.print3
                       "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                       (FStar_String.concat ", " all_files_0) uu____5924
                       (FStar_String.concat ", " interfaces_needing_inlining)
                   else ());
                  (let dep_graph2 = widen_deps friends dep_graph1  in
                   let uu____5945 =
                     (let uu____5957 = FStar_Options.debug_any ()  in
                      if uu____5957
                      then
                        FStar_Util.print_string
                          "==============Phase2==================\n"
                      else ());
                     all_friend_deps dep_graph2 [] ([], []) root_files  in
                   match uu____5945 with
                   | (uu____5980,all_files) ->
                       ((let uu____5995 = FStar_Options.debug_any ()  in
                         if uu____5995
                         then
                           FStar_Util.print1
                             "Phase2 complete: all_files = %s\n"
                             (FStar_String.concat ", " all_files)
                         else ());
                        (let uu____6002 = FStar_ST.op_Bang widened  in
                         (all_files, uu____6002))))))
  
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
                let uu____6088 = FStar_Options.find_file fn  in
                match uu____6088 with
                | FStar_Pervasives_Native.None  ->
                    let uu____6094 =
                      let uu____6100 =
                        FStar_Util.format1 "File %s could not be found\n" fn
                         in
                      (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____6100)
                       in
                    FStar_Errors.raise_err uu____6094
                | FStar_Pervasives_Native.Some fn1 -> fn1))
         in
      let dep_graph = deps_empty ()  in
      let file_system_map = build_map all_cmd_line_files1  in
      let interfaces_needing_inlining = FStar_Util.mk_ref []  in
      let add_interface_for_inlining l =
        let l1 = lowercase_module_name l  in
        let uu____6130 =
          let uu____6134 = FStar_ST.op_Bang interfaces_needing_inlining  in
          l1 :: uu____6134  in
        FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6130  in
      let parse_results = FStar_Util.smap_create (Prims.parse_int "40")  in
      let rec discover_one file_name =
        let uu____6201 =
          let uu____6203 = deps_try_find dep_graph file_name  in
          uu____6203 = FStar_Pervasives_Native.None  in
        if uu____6201
        then
          let uu____6209 =
            let uu____6225 =
              let uu____6239 = FStar_ST.op_Bang collect_one_cache  in
              FStar_Util.smap_try_find uu____6239 file_name  in
            match uu____6225 with
            | FStar_Pervasives_Native.Some cached -> ((Mk_pd []), cached)
            | FStar_Pervasives_Native.None  ->
                let uu____6369 =
                  collect_one file_system_map file_name
                    get_parsing_data_from_cache
                   in
                (match uu____6369 with
                 | (parsing_data,deps,needs_interface_inlining,additional_roots)
                     ->
                     (parsing_data,
                       (deps, additional_roots, needs_interface_inlining)))
             in
          match uu____6209 with
          | (parsing_data,(deps,mo_roots,needs_interface_inlining)) ->
              (if needs_interface_inlining
               then add_interface_for_inlining file_name
               else ();
               FStar_Util.smap_add parse_results file_name parsing_data;
               (let deps1 =
                  let module_name = lowercase_module_name file_name  in
                  let uu____6463 =
                    (is_implementation file_name) &&
                      (has_interface file_system_map module_name)
                     in
                  if uu____6463
                  then FStar_List.append deps [UseInterface module_name]
                  else deps  in
                let dep_node =
                  let uu____6471 = FStar_List.unique deps1  in
                  { edges = uu____6471; color = White }  in
                deps_add_dep dep_graph file_name dep_node;
                (let uu____6473 =
                   FStar_List.map
                     (file_of_dep file_system_map all_cmd_line_files1)
                     (FStar_List.append deps1 mo_roots)
                    in
                 FStar_List.iter discover_one uu____6473)))
        else ()  in
      FStar_Options.profile
        (fun uu____6483  -> FStar_List.iter discover_one all_cmd_line_files1)
        (fun uu____6486  -> "Dependence analysis: Initial scan");
      (let cycle_detected dep_graph1 cycle filename =
         FStar_Util.print1
           "The cycle contains a subset of the modules in:\n%s \n"
           (FStar_String.concat "\n`used by` " cycle);
         print_graph dep_graph1;
         FStar_Util.print_string "\n";
         (let uu____6518 =
            let uu____6524 =
              FStar_Util.format1 "Recursive dependency on module %s\n"
                filename
               in
            (FStar_Errors.Fatal_CyclicDependence, uu____6524)  in
          FStar_Errors.raise_err uu____6518)
          in
       let full_cycle_detection all_command_line_files file_system_map1 =
         let dep_graph1 = dep_graph_copy dep_graph  in
         let mo_files = FStar_Util.mk_ref []  in
         let rec aux cycle filename =
           let node =
             let uu____6576 = deps_try_find dep_graph1 filename  in
             match uu____6576 with
             | FStar_Pervasives_Native.Some node -> node
             | FStar_Pervasives_Native.None  ->
                 let uu____6580 =
                   FStar_Util.format1 "Failed to find dependences of %s"
                     filename
                    in
                 failwith uu____6580
              in
           let direct_deps =
             FStar_All.pipe_right node.edges
               (FStar_List.collect
                  (fun x  ->
                     match x with
                     | UseInterface f ->
                         let uu____6594 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6594 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6605 -> [x; UseImplementation f])
                     | PreferInterface f ->
                         let uu____6611 =
                           implementation_of_internal file_system_map1 f  in
                         (match uu____6611 with
                          | FStar_Pervasives_Native.None  -> [x]
                          | FStar_Pervasives_Native.Some fn when
                              fn = filename -> [x]
                          | uu____6622 -> [x; UseImplementation f])
                     | uu____6626 -> [x]))
              in
           match node.color with
           | Gray  -> cycle_detected dep_graph1 cycle filename
           | Black  -> ()
           | White  ->
               (deps_add_dep dep_graph1 filename
                  (let uu___1113_6629 = node  in
                   { edges = direct_deps; color = Gray });
                (let uu____6631 =
                   dependences_of file_system_map1 dep_graph1
                     all_command_line_files filename
                    in
                 FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____6631);
                deps_add_dep dep_graph1 filename
                  (let uu___1118_6642 = node  in
                   { edges = direct_deps; color = Black });
                (let uu____6643 = is_interface filename  in
                 if uu____6643
                 then
                   let uu____6646 =
                     let uu____6650 = lowercase_module_name filename  in
                     implementation_of_internal file_system_map1 uu____6650
                      in
                   FStar_Util.iter_opt uu____6646
                     (fun impl  ->
                        if
                          Prims.op_Negation
                            (FStar_List.contains impl all_command_line_files)
                        then
                          let uu____6659 =
                            let uu____6663 = FStar_ST.op_Bang mo_files  in
                            impl :: uu____6663  in
                          FStar_ST.op_Colon_Equals mo_files uu____6659
                        else ())
                 else ()))
            in
         FStar_List.iter (aux []) all_command_line_files;
         (let uu____6725 = FStar_ST.op_Bang mo_files  in
          FStar_List.iter (aux []) uu____6725)
          in
       full_cycle_detection all_cmd_line_files1 file_system_map;
       FStar_All.pipe_right all_cmd_line_files1
         (FStar_List.iter
            (fun f  ->
               let m = lowercase_module_name f  in
               FStar_Options.add_verify_module m));
       (let inlining_ifaces = FStar_ST.op_Bang interfaces_needing_inlining
           in
        let uu____6797 =
          FStar_Options.profile
            (fun uu____6816  ->
               let uu____6817 =
                 let uu____6819 = FStar_Options.codegen ()  in
                 uu____6819 <> FStar_Pervasives_Native.None  in
               topological_dependences_of file_system_map dep_graph
                 inlining_ifaces all_cmd_line_files1 uu____6817)
            (fun uu____6825  ->
               "Dependence analysis: topological sort for full file list")
           in
        match uu____6797 with
        | (all_files,uu____6843) ->
            ((let uu____6853 = FStar_Options.debug_any ()  in
              if uu____6853
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
    let uu____6906 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____6932  ->
              match uu____6932 with
              | (m,d) ->
                  let uu____6946 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____6946))
       in
    FStar_All.pipe_right uu____6906 (FStar_String.concat "\n")
  
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
              let uu____6981 = deps_try_find deps1 f  in
              FStar_All.pipe_right uu____6981 FStar_Option.get  in
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
    let uu____7010 = deps.dep_graph  in
    match uu____7010 with
    | Deps deps1 ->
        let uu____7014 =
          let uu____7016 =
            FStar_Util.smap_fold deps1
              (fun k  ->
                 fun dep_node  ->
                   fun out  ->
                     let uu____7034 =
                       let uu____7036 =
                         let uu____7038 =
                           FStar_List.map dep_to_string dep_node.edges  in
                         FStar_All.pipe_right uu____7038
                           (FStar_String.concat ";\n\t")
                          in
                       FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7036
                        in
                     uu____7034 :: out) []
             in
          FStar_All.pipe_right uu____7016 (FStar_String.concat ";;\n")  in
        FStar_All.pipe_right uu____7014 FStar_Util.print_endline
  
let (print_full : deps -> unit) =
  fun deps  ->
    let sort_output_files orig_output_file_map =
      let order = FStar_Util.mk_ref []  in
      let remaining_output_files = FStar_Util.smap_copy orig_output_file_map
         in
      let visited_other_modules =
        FStar_Util.smap_create (Prims.parse_int "41")  in
      let should_visit lc_module_name =
        (let uu____7110 =
           FStar_Util.smap_try_find remaining_output_files lc_module_name  in
         FStar_Option.isSome uu____7110) ||
          (let uu____7117 =
             FStar_Util.smap_try_find visited_other_modules lc_module_name
              in
           FStar_Option.isNone uu____7117)
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
            let uu____7160 =
              let uu____7164 = FStar_ST.op_Bang order  in ml_file ::
                uu____7164
               in
            FStar_ST.op_Colon_Equals order uu____7160
         in
      let rec aux uu___15_7227 =
        match uu___15_7227 with
        | [] -> ()
        | lc_module_name::modules_to_extract ->
            let visit_file file_opt =
              match file_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some file_name ->
                  let uu____7255 = deps_try_find deps.dep_graph file_name  in
                  (match uu____7255 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____7258 =
                         FStar_Util.format2
                           "Impossible: module %s: %s not found"
                           lc_module_name file_name
                          in
                       failwith uu____7258
                   | FStar_Pervasives_Native.Some
                       { edges = immediate_deps; color = uu____7262;_} ->
                       let immediate_deps1 =
                         FStar_List.map
                           (fun x  ->
                              FStar_String.lowercase (module_name_of_dep x))
                           immediate_deps
                          in
                       aux immediate_deps1)
               in
            ((let uu____7271 = should_visit lc_module_name  in
              if uu____7271
              then
                let ml_file_opt = mark_visiting lc_module_name  in
                ((let uu____7279 = implementation_of deps lc_module_name  in
                  visit_file uu____7279);
                 (let uu____7284 = interface_of deps lc_module_name  in
                  visit_file uu____7284);
                 emit_output_file_opt ml_file_opt)
              else ());
             aux modules_to_extract)
         in
      let all_extracted_modules = FStar_Util.smap_keys orig_output_file_map
         in
      aux all_extracted_modules;
      (let uu____7296 = FStar_ST.op_Bang order  in FStar_List.rev uu____7296)
       in
    let sb =
      let uu____7327 = FStar_BigInt.of_int_fs (Prims.parse_int "10000")  in
      FStar_StringBuffer.create uu____7327  in
    let pr str =
      let uu____7337 = FStar_StringBuffer.add str sb  in
      FStar_All.pipe_left (fun a1  -> ()) uu____7337  in
    let print_entry target first_dep all_deps =
      pr target; pr ": "; pr first_dep; pr "\\\n\t"; pr all_deps; pr "\n\n"
       in
    let keys = deps_keys deps.dep_graph  in
    let output_file ext fst_file =
      let ml_base_name =
        let uu____7390 =
          let uu____7392 =
            let uu____7396 = FStar_Util.basename fst_file  in
            check_and_strip_suffix uu____7396  in
          FStar_Option.get uu____7392  in
        FStar_Util.replace_chars uu____7390 46 "_"  in
      let uu____7401 = FStar_String.op_Hat ml_base_name ext  in
      FStar_Options.prepend_output_dir uu____7401  in
    let norm_path s = FStar_Util.replace_chars s 92 "/"  in
    let output_ml_file f =
      let uu____7423 = output_file ".ml" f  in norm_path uu____7423  in
    let output_krml_file f =
      let uu____7435 = output_file ".krml" f  in norm_path uu____7435  in
    let output_cmx_file f =
      let uu____7447 = output_file ".cmx" f  in norm_path uu____7447  in
    let cache_file f =
      let uu____7459 = cache_file_name f  in norm_path uu____7459  in
    let all_checked_files =
      FStar_All.pipe_right keys
        (FStar_List.fold_left
           (fun all_checked_files  ->
              fun file_name  ->
                let process_one_key uu____7492 =
                  let dep_node =
                    let uu____7494 = deps_try_find deps.dep_graph file_name
                       in
                    FStar_All.pipe_right uu____7494 FStar_Option.get  in
                  let iface_deps =
                    let uu____7504 = is_interface file_name  in
                    if uu____7504
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____7515 =
                         let uu____7519 = lowercase_module_name file_name  in
                         interface_of deps uu____7519  in
                       match uu____7515 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some iface ->
                           let uu____7531 =
                             let uu____7534 =
                               let uu____7535 =
                                 deps_try_find deps.dep_graph iface  in
                               FStar_Option.get uu____7535  in
                             uu____7534.edges  in
                           FStar_Pervasives_Native.Some uu____7531)
                     in
                  let iface_deps1 =
                    FStar_Util.map_opt iface_deps
                      (FStar_List.filter
                         (fun iface_dep  ->
                            let uu____7552 =
                              FStar_Util.for_some (dep_subsumed_by iface_dep)
                                dep_node.edges
                               in
                            Prims.op_Negation uu____7552))
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
                      (fun uu____7612  -> FStar_String.concat "\\\n\t" files3)
                      (fun uu____7615  -> "Dependence analysis: concat files")
                     in
                  let cache_file_name1 = cache_file file_name  in
                  let all_checked_files1 =
                    let uu____7624 =
                      let uu____7626 =
                        let uu____7628 = module_name_of_file file_name  in
                        FStar_Options.should_be_already_cached uu____7628  in
                      Prims.op_Negation uu____7626  in
                    if uu____7624
                    then
                      (print_entry cache_file_name1 norm_f files4;
                       cache_file_name1
                       ::
                       all_checked_files)
                    else all_checked_files  in
                  let uu____7638 =
                    let uu____7647 = FStar_Options.cmi ()  in
                    if uu____7647
                    then
                      FStar_Options.profile
                        (fun uu____7667  ->
                           topological_dependences_of deps.file_system_map
                             deps.dep_graph deps.interfaces_with_inlining
                             [file_name] true)
                        (fun uu____7672  ->
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
                       let uu____7716 =
                         FStar_Util.remove_dups (fun x  -> fun y  -> x = y)
                           (FStar_List.append fst_files fst_files_from_iface)
                          in
                       (uu____7716, false))
                     in
                  match uu____7638 with
                  | (all_fst_files_dep,widened) ->
                      let all_checked_fst_dep_files =
                        FStar_All.pipe_right all_fst_files_dep
                          (FStar_List.map cache_file)
                         in
                      let all_checked_fst_dep_files_string =
                        FStar_String.concat " \\\n\t"
                          all_checked_fst_dep_files
                         in
                      ((let uu____7763 = is_implementation file_name  in
                        if uu____7763
                        then
                          ((let uu____7767 =
                              (FStar_Options.cmi ()) && widened  in
                            if uu____7767
                            then
                              ((let uu____7771 = output_ml_file file_name  in
                                print_entry uu____7771 cache_file_name1
                                  all_checked_fst_dep_files_string);
                               (let uu____7773 = output_krml_file file_name
                                   in
                                print_entry uu____7773 cache_file_name1
                                  all_checked_fst_dep_files_string))
                            else
                              ((let uu____7778 = output_ml_file file_name  in
                                print_entry uu____7778 cache_file_name1 "");
                               (let uu____7781 = output_krml_file file_name
                                   in
                                print_entry uu____7781 cache_file_name1 "")));
                           (let cmx_files =
                              let extracted_fst_files =
                                FStar_All.pipe_right all_fst_files_dep
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____7806 =
                                           lowercase_module_name df  in
                                         let uu____7808 =
                                           lowercase_module_name file_name
                                            in
                                         uu____7806 <> uu____7808) &&
                                          (let uu____7812 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____7812)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            let uu____7822 =
                              let uu____7824 =
                                lowercase_module_name file_name  in
                              FStar_Options.should_extract uu____7824  in
                            if uu____7822
                            then
                              let cmx_files1 =
                                FStar_String.concat "\\\n\t" cmx_files  in
                              let uu____7830 = output_cmx_file file_name  in
                              let uu____7832 = output_ml_file file_name  in
                              print_entry uu____7830 uu____7832 cmx_files1
                            else ()))
                        else
                          (let uu____7838 =
                             (let uu____7842 =
                                let uu____7844 =
                                  lowercase_module_name file_name  in
                                has_implementation deps.file_system_map
                                  uu____7844
                                 in
                              Prims.op_Negation uu____7842) &&
                               (is_interface file_name)
                              in
                           if uu____7838
                           then
                             let uu____7847 =
                               (FStar_Options.cmi ()) && (widened || true)
                                in
                             (if uu____7847
                              then
                                let uu____7851 = output_krml_file file_name
                                   in
                                print_entry uu____7851 cache_file_name1
                                  all_checked_fst_dep_files_string
                              else
                                (let uu____7855 = output_krml_file file_name
                                    in
                                 print_entry uu____7855 cache_file_name1 ""))
                           else ()));
                       all_checked_files1)
                   in
                FStar_Options.profile process_one_key
                  (fun uu____7864  ->
                     FStar_Util.format1 "Dependence analysis: output key %s"
                       file_name)) [])
       in
    let all_fst_files =
      let uu____7874 =
        FStar_All.pipe_right keys (FStar_List.filter is_implementation)  in
      FStar_All.pipe_right uu____7874
        (FStar_Util.sort_with FStar_String.compare)
       in
    let all_ml_files =
      let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right all_fst_files
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____7915 = FStar_Options.should_extract mname  in
              if uu____7915
              then
                let uu____7918 = output_ml_file fst_file  in
                FStar_Util.smap_add ml_file_map mname uu____7918
              else ()));
      sort_output_files ml_file_map  in
    let all_krml_files =
      let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun fst_file  ->
              let mname = lowercase_module_name fst_file  in
              let uu____7945 = output_krml_file fst_file  in
              FStar_Util.smap_add krml_file_map mname uu____7945));
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
    let uu____7993 = FStar_Options.dep ()  in
    match uu____7993 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" ->
        FStar_Options.profile (fun uu____8002  -> print_full deps)
          (fun uu____8004  -> "Dependence analysis: printing")
    | FStar_Pervasives_Native.Some "graph" -> print_graph deps.dep_graph
    | FStar_Pervasives_Native.Some "raw" -> print_raw deps
    | FStar_Pervasives_Native.Some uu____8010 ->
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
         fun uu____8065  ->
           fun s  ->
             match uu____8065 with
             | (v0,v1) ->
                 let uu____8094 =
                   let uu____8096 =
                     FStar_Util.format3 "%s -> (%s, %s)" k
                       (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1)
                      in
                   FStar_String.op_Hat "; " uu____8096  in
                 FStar_String.op_Hat s uu____8094) ""
  
let (module_has_interface : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let uu____8117 =
        let uu____8119 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8119  in
      has_interface deps.file_system_map uu____8117
  
let (deps_has_implementation : deps -> FStar_Ident.lident -> Prims.bool) =
  fun deps  ->
    fun module_name  ->
      let m =
        let uu____8135 = FStar_Ident.string_of_lid module_name  in
        FStar_String.lowercase uu____8135  in
      FStar_All.pipe_right deps.all_files
        (FStar_Util.for_some
           (fun f  ->
              (is_implementation f) &&
                (let uu____8146 =
                   let uu____8148 = module_name_of_file f  in
                   FStar_String.lowercase uu____8148  in
                 uu____8146 = m)))
  