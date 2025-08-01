open Prims
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu___ -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu___ -> false
type module_name = Prims.string
let (dbg : Prims.bool FStarC_Effect.ref) = FStarC_Debug.get_toggle "Dep"
let (dbg_CheckedFiles : Prims.bool FStarC_Effect.ref) =
  FStarC_Debug.get_toggle "CheckedFiles"
let profile : 'uuuuu . (unit -> 'uuuuu) -> Prims.string -> 'uuuuu =
  fun f -> fun c -> FStarC_Profiling.profile f FStar_Pervasives_Native.None c
let with_file_outchannel :
  'a . Prims.string -> (FStarC_Util.out_channel -> 'a) -> 'a =
  fun fn ->
    fun k ->
      FStarC_Util.maybe_create_parent fn;
      (let outc = FStarC_Util.open_file_for_writing fn in
       let r =
         try (fun uu___1 -> match () with | () -> k outc) ()
         with
         | uu___1 ->
             (FStarC_Util.close_out_channel outc;
              FStarC_Util.delete_file fn;
              FStarC_Effect.raise uu___1) in
       FStarC_Util.close_out_channel outc; r)
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee -> match projectee with | VerifyAll -> true | uu___ -> false
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyUserList -> true | uu___ -> false
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyFigureItOut -> true | uu___ -> false
type intf_and_impl =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)
type files_for_module_name = intf_and_impl FStarC_SMap.t
let (intf_and_impl_to_string :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun ii ->
    match ii with
    | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
        "<None>, <None>"
    | (FStar_Pervasives_Native.Some intf, FStar_Pervasives_Native.None) ->
        intf
    | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some impl) ->
        impl
    | (FStar_Pervasives_Native.Some intf, FStar_Pervasives_Native.Some impl)
        -> Prims.strcat intf (Prims.strcat ", " impl)
let (files_for_module_name_to_string : files_for_module_name -> unit) =
  fun m ->
    FStarC_Format.print_string "Printing the file system map {\n";
    (let str_opt_to_string sopt =
       match sopt with
       | FStar_Pervasives_Native.None -> "<None>"
       | FStar_Pervasives_Native.Some s -> s in
     FStarC_SMap.iter m
       (fun k ->
          fun v ->
            FStarC_Format.print2 "%s:%s\n" k (intf_and_impl_to_string v));
     FStarC_Format.print_string "}\n")
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee -> match projectee with | White -> true | uu___ -> false
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee -> match projectee with | Gray -> true | uu___ -> false
let (uu___is_Black : color -> Prims.bool) =
  fun projectee -> match projectee with | Black -> true | uu___ -> false
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f ->
    let suffixes = [".fsti"; ".fst"] in
    let matches =
      FStarC_List.map
        (fun ext ->
           let lext = FStarC_String.length ext in
           let l = FStarC_String.length f in
           let uu___ =
             (l > lext) &&
               (let uu___1 = FStarC_String.substring f (l - lext) lext in
                uu___1 = ext) in
           if uu___
           then
             let uu___1 = FStarC_String.substring f Prims.int_zero (l - lext) in
             FStar_Pervasives_Native.Some uu___1
           else FStar_Pervasives_Native.None) suffixes in
    let uu___ =
      FStarC_List.filter FStar_Pervasives_Native.uu___is_Some matches in
    match uu___ with
    | (FStar_Pervasives_Native.Some m)::uu___1 ->
        FStar_Pervasives_Native.Some m
    | uu___1 -> FStar_Pervasives_Native.None
let (is_interface : Prims.string -> Prims.bool) =
  fun f ->
    let uu___ =
      FStarC_String.get f ((FStarC_String.length f) - Prims.int_one) in
    uu___ = 105
let (is_implementation : Prims.string -> Prims.bool) =
  fun f -> let uu___ = is_interface f in Prims.op_Negation uu___
let list_of_option :
  'uuuuu . 'uuuuu FStar_Pervasives_Native.option -> 'uuuuu Prims.list =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None -> []
let list_of_pair :
  'uuuuu .
    ('uuuuu FStar_Pervasives_Native.option * 'uuuuu
      FStar_Pervasives_Native.option) -> 'uuuuu Prims.list
  =
  fun uu___ ->
    match uu___ with
    | (intf, impl) ->
        FStarC_List.op_At (list_of_option intf) (list_of_option impl)
let (maybe_module_name_of_file :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f ->
    let uu___ = FStarC_Filepath.basename f in check_and_strip_suffix uu___
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f ->
    let uu___ = maybe_module_name_of_file f in
    match uu___ with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Format.fmt1 "Not a valid FStar file: '%s'" f in
              FStarC_Errors_Msg.text uu___4 in
            [uu___3] in
          let uu___3 =
            if FStarC_Platform.windows && (f = "..")
            then
              let uu___4 =
                FStarC_Errors_Msg.text
                  "Note: In Windows-compiled versions of F*, a literal\n          asterisk as argument will be expanded to a list of files,\n          **even if quoted**. It is possible you provided such an\n          argument which got expanded to the list of all files in this\n          directory, causing spurious arguments that F* attempts to interpret as files." in
              let uu___5 =
                let uu___6 =
                  FStarC_Errors_Msg.text
                    "Hint: did you perhaps pass --already_cached '*' or similar? You can add\n          a comma (',*') to prevent the expansion and retain the behavior." in
                [uu___6] in
              uu___4 :: uu___5
            else [] in
          FStarC_List.op_At uu___2 uu___3 in
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Fatal_NotValidFStarFile ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___1)
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f -> let uu___ = module_name_of_file f in FStarC_String.lowercase uu___
let (namespace_of_module :
  Prims.string -> FStarC_Ident.lident FStar_Pervasives_Native.option) =
  fun f ->
    let lid =
      let uu___ = FStarC_Ident.path_of_text f in
      FStarC_Ident.lid_of_path uu___ FStarC_Range_Type.dummyRange in
    let uu___ = FStarC_Ident.ns_of_lid lid in
    match uu___ with
    | [] -> FStar_Pervasives_Native.None
    | ns ->
        let uu___1 = FStarC_Ident.lid_of_ids ns in
        FStar_Pervasives_Native.Some uu___1
type file_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
  | FriendImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | UseInterface _0 -> true | uu___ -> false
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | UseInterface _0 -> _0
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | PreferInterface _0 -> true | uu___ -> false
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | PreferInterface _0 -> _0
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | UseImplementation _0 -> true | uu___ -> false
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | UseImplementation _0 -> _0
let (uu___is_FriendImplementation : dependence -> Prims.bool) =
  fun projectee ->
    match projectee with | FriendImplementation _0 -> true | uu___ -> false
let (__proj__FriendImplementation__item___0 : dependence -> module_name) =
  fun projectee -> match projectee with | FriendImplementation _0 -> _0
let (dep_to_string : dependence -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | UseInterface f -> Prims.strcat "UseInterface " f
    | PreferInterface f -> Prims.strcat "PreferInterface " f
    | UseImplementation f -> Prims.strcat "UseImplementation " f
    | FriendImplementation f -> Prims.strcat "FriendImplementation " f
let (showable_dependence : dependence FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = dep_to_string }
type dependences = dependence Prims.list
let empty_dependences : 'uuuuu . unit -> 'uuuuu Prims.list = fun uu___ -> []
type dep_node = {
  edges: dependences ;
  color: color }
let (__proj__Mkdep_node__item__edges : dep_node -> dependences) =
  fun projectee -> match projectee with | { edges; color = color1;_} -> edges
let (__proj__Mkdep_node__item__color : dep_node -> color) =
  fun projectee ->
    match projectee with | { edges; color = color1;_} -> color1
type dependence_graph =
  | Deps of dep_node FStarC_SMap.t 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee -> true
let (__proj__Deps__item___0 : dependence_graph -> dep_node FStarC_SMap.t) =
  fun projectee -> match projectee with | Deps _0 -> _0
type parsing_data_elt =
  | P_begin_module of FStarC_Ident.lident 
  | P_open of (Prims.bool * FStarC_Ident.lident) 
  | P_implicit_open_module_or_namespace of (open_kind * FStarC_Ident.lid) 
  | P_dep of (Prims.bool * FStarC_Ident.lident) 
  | P_alias of (FStarC_Ident.ident * FStarC_Ident.lident) 
  | P_lid of FStarC_Ident.lident 
  | P_inline_for_extraction 
let (uu___is_P_begin_module : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_begin_module _0 -> true | uu___ -> false
let (__proj__P_begin_module__item___0 :
  parsing_data_elt -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | P_begin_module _0 -> _0
let (uu___is_P_open : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_open _0 -> true | uu___ -> false
let (__proj__P_open__item___0 :
  parsing_data_elt -> (Prims.bool * FStarC_Ident.lident)) =
  fun projectee -> match projectee with | P_open _0 -> _0
let (uu___is_P_implicit_open_module_or_namespace :
  parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with
    | P_implicit_open_module_or_namespace _0 -> true
    | uu___ -> false
let (__proj__P_implicit_open_module_or_namespace__item___0 :
  parsing_data_elt -> (open_kind * FStarC_Ident.lid)) =
  fun projectee ->
    match projectee with | P_implicit_open_module_or_namespace _0 -> _0
let (uu___is_P_dep : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_dep _0 -> true | uu___ -> false
let (__proj__P_dep__item___0 :
  parsing_data_elt -> (Prims.bool * FStarC_Ident.lident)) =
  fun projectee -> match projectee with | P_dep _0 -> _0
let (uu___is_P_alias : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_alias _0 -> true | uu___ -> false
let (__proj__P_alias__item___0 :
  parsing_data_elt -> (FStarC_Ident.ident * FStarC_Ident.lident)) =
  fun projectee -> match projectee with | P_alias _0 -> _0
let (uu___is_P_lid : parsing_data_elt -> Prims.bool) =
  fun projectee -> match projectee with | P_lid _0 -> true | uu___ -> false
let (__proj__P_lid__item___0 : parsing_data_elt -> FStarC_Ident.lident) =
  fun projectee -> match projectee with | P_lid _0 -> _0
let (uu___is_P_inline_for_extraction : parsing_data_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | P_inline_for_extraction -> true | uu___ -> false
type parsing_data =
  {
  elts: parsing_data_elt Prims.list ;
  no_prelude: Prims.bool }
let (__proj__Mkparsing_data__item__elts :
  parsing_data -> parsing_data_elt Prims.list) =
  fun projectee -> match projectee with | { elts; no_prelude;_} -> elts
let (__proj__Mkparsing_data__item__no_prelude : parsing_data -> Prims.bool) =
  fun projectee -> match projectee with | { elts; no_prelude;_} -> no_prelude
let (str_of_parsing_data_elt : parsing_data_elt -> Prims.string) =
  fun elt ->
    let str_of_open_kind uu___ =
      match uu___ with
      | Open_module -> "P_open_module"
      | Open_namespace -> "P_open_namespace" in
    match elt with
    | P_begin_module lid ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid lid in
          Prims.strcat uu___1 ")" in
        Prims.strcat "P_begin_module (" uu___
    | P_open (b, lid) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.string_of_lid lid in
              Prims.strcat uu___4 ")" in
            Prims.strcat ", " uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "P_open (" uu___
    | P_implicit_open_module_or_namespace (k, lid) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Ident.string_of_lid lid in
              Prims.strcat uu___3 ")" in
            Prims.strcat ", " uu___2 in
          Prims.strcat (str_of_open_kind k) uu___1 in
        Prims.strcat "P_implicit_open_module_or_namespace (" uu___
    | P_dep (b, lid) ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid lid in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
              Prims.strcat uu___4 ")" in
            Prims.strcat ", " uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "P_dep (" uu___
    | P_alias (id, lid) ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_id id in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.string_of_lid lid in
              Prims.strcat uu___4 ")" in
            Prims.strcat ", " uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "P_alias (" uu___
    | P_lid lid ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid lid in
          Prims.strcat uu___1 ")" in
        Prims.strcat "P_lid (" uu___
    | P_inline_for_extraction -> "P_inline_for_extraction"
let (showable_parsing_data_elt : parsing_data_elt FStarC_Class_Show.showable)
  = { FStarC_Class_Show.show = str_of_parsing_data_elt }
let (str_of_parsing_data : parsing_data -> Prims.string) =
  fun pd ->
    let uu___ =
      let uu___1 =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list showable_parsing_data_elt) pd.elts in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool
              pd.no_prelude in
          Prims.strcat uu___4 "}" in
        Prims.strcat "; no_prelude = " uu___3 in
      Prims.strcat uu___1 uu___2 in
    Prims.strcat "{ elts = " uu___
let (showable_parsing_data : parsing_data FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = str_of_parsing_data }
let (friends : parsing_data -> FStarC_Ident.lident Prims.list) =
  fun p ->
    FStarC_List.collect
      (fun uu___ -> match uu___ with | P_dep (true, l) -> [l] | uu___1 -> [])
      p.elts
let (parsing_data_elt_eq :
  parsing_data_elt -> parsing_data_elt -> Prims.bool) =
  fun e1 ->
    fun e2 ->
      match (e1, e2) with
      | (P_begin_module l1, P_begin_module l2) ->
          FStarC_Ident.lid_equals l1 l2
      | (P_open (b1, l1), P_open (b2, l2)) ->
          (b1 = b2) && (FStarC_Ident.lid_equals l1 l2)
      | (P_implicit_open_module_or_namespace (k1, l1),
         P_implicit_open_module_or_namespace (k2, l2)) ->
          (k1 = k2) && (FStarC_Ident.lid_equals l1 l2)
      | (P_dep (b1, l1), P_dep (b2, l2)) ->
          (b1 = b2) && (FStarC_Ident.lid_equals l1 l2)
      | (P_alias (i1, l1), P_alias (i2, l2)) ->
          (let uu___ = FStarC_Ident.string_of_id i1 in
           let uu___1 = FStarC_Ident.string_of_id i2 in uu___ = uu___1) &&
            (FStarC_Ident.lid_equals l1 l2)
      | (P_lid l1, P_lid l2) -> FStarC_Ident.lid_equals l1 l2
      | (P_inline_for_extraction, P_inline_for_extraction) -> true
      | (uu___, uu___1) -> false
let (empty_parsing_data : parsing_data) = { elts = []; no_prelude = false }
type deps =
  {
  dep_graph: dependence_graph ;
  file_system_map: files_for_module_name ;
  cmd_line_files: file_name Prims.list ;
  all_files: file_name Prims.list ;
  interfaces_with_inlining: module_name Prims.list ;
  parse_results: parsing_data FStarC_SMap.t }
let (__proj__Mkdeps__item__dep_graph : deps -> dependence_graph) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> dep_graph
let (__proj__Mkdeps__item__file_system_map : deps -> files_for_module_name) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> file_system_map
let (__proj__Mkdeps__item__cmd_line_files : deps -> file_name Prims.list) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> cmd_line_files
let (__proj__Mkdeps__item__all_files : deps -> file_name Prims.list) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> all_files
let (__proj__Mkdeps__item__interfaces_with_inlining :
  deps -> module_name Prims.list) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} ->
        interfaces_with_inlining
let (__proj__Mkdeps__item__parse_results :
  deps -> parsing_data FStarC_SMap.t) =
  fun projectee ->
    match projectee with
    | { dep_graph; file_system_map; cmd_line_files; all_files;
        interfaces_with_inlining; parse_results;_} -> parse_results
let (deps_try_find :
  dependence_graph -> Prims.string -> dep_node FStar_Pervasives_Native.option)
  =
  fun uu___ -> fun k -> match uu___ with | Deps m -> FStarC_SMap.try_find m k
let (deps_add_dep : dependence_graph -> Prims.string -> dep_node -> unit) =
  fun uu___ ->
    fun k -> fun v -> match uu___ with | Deps m -> FStarC_SMap.add m k v
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu___ -> match uu___ with | Deps m -> FStarC_SMap.keys m
let (deps_empty : unit -> dependence_graph) =
  fun uu___ ->
    let uu___1 = FStarC_SMap.create (Prims.of_int (41)) in Deps uu___1
let (mk_deps :
  dependence_graph ->
    files_for_module_name ->
      file_name Prims.list ->
        file_name Prims.list ->
          module_name Prims.list -> parsing_data FStarC_SMap.t -> deps)
  =
  fun dg ->
    fun fs ->
      fun c ->
        fun a ->
          fun i ->
            fun pr ->
              {
                dep_graph = dg;
                file_system_map = fs;
                cmd_line_files = c;
                all_files = a;
                interfaces_with_inlining = i;
                parse_results = pr
              }
let (empty_deps : deps) =
  let uu___ = deps_empty () in
  let uu___1 = FStarC_SMap.create Prims.int_zero in
  let uu___2 = FStarC_SMap.create Prims.int_zero in
  mk_deps uu___ uu___1 [] [] [] uu___2
let (module_name_of_dep : dependence -> module_name) =
  fun uu___ ->
    match uu___ with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
    | FriendImplementation m -> m
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = FStarC_SMap.try_find file_system_map key in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn, uu___1) ->
          let uu___2 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu___2
      | FStar_Pervasives_Native.Some
          (uu___1, FStar_Pervasives_Native.Some fn) ->
          let uu___2 = lowercase_module_name fn in
          FStar_Pervasives_Native.Some uu___2
      | uu___1 -> FStar_Pervasives_Native.None
let (interface_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = FStarC_SMap.try_find file_system_map key in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface, uu___1) ->
          FStar_Pervasives_Native.Some iface
      | uu___1 -> FStar_Pervasives_Native.None
let (implementation_of_internal :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = FStarC_SMap.try_find file_system_map key in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (uu___1, FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu___1 -> FStar_Pervasives_Native.None
let (interface_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps1 -> fun key -> interface_of_internal deps1.file_system_map key
let (implementation_of :
  deps -> Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun deps1 ->
    fun key -> implementation_of_internal deps1.file_system_map key
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map ->
    fun key ->
      let uu___ = interface_of_internal file_system_map key in
      FStar_Pervasives_Native.uu___is_Some uu___
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map ->
    fun key ->
      let uu___ = implementation_of_internal file_system_map key in
      FStar_Pervasives_Native.uu___is_Some uu___
let (cache_file_name : Prims.string -> Prims.string) =
  let checked_file_and_exists_flag fn =
    let cache_fn =
      let lax = FStarC_Options.lax () in
      if lax
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked" in
    let mname = module_name_of_file fn in
    let uu___ =
      let uu___1 = FStarC_Filepath.basename cache_fn in
      FStarC_Find.find_file uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some path ->
        let expected_cache_file = FStarC_Find.prepend_cache_dir cache_fn in
        ((let uu___2 =
            ((let uu___3 = FStarC_Options.dep () in
              FStar_Pervasives_Native.uu___is_Some uu___3) &&
               (let uu___3 = FStarC_Options.should_be_already_cached mname in
                Prims.op_Negation uu___3))
              &&
              ((Prims.op_Negation
                  (FStarC_Filepath.file_exists expected_cache_file))
                 ||
                 (let uu___3 =
                    FStarC_Filepath.paths_to_same_file path
                      expected_cache_file in
                  Prims.op_Negation uu___3)) in
          if uu___2
          then
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Errors_Msg.text "Did not expect module" in
                let uu___6 =
                  let uu___7 = FStarC_Pprint.doc_of_string mname in
                  let uu___8 =
                    FStarC_Errors_Msg.text "to be already checked." in
                  FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_Errors_Msg.text
                        "Found it in an unexpected location:" in
                    let uu___9 = FStarC_Pprint.doc_of_string path in
                    FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___8 uu___9 in
                  let uu___8 =
                    let uu___9 = FStarC_Errors_Msg.text "instead of" in
                    let uu___10 =
                      FStarC_Pprint.doc_of_string expected_cache_file in
                    FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___9 uu___10 in
                  FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                [uu___6] in
              uu___4 :: uu___5 in
            FStarC_Errors.log_issue0
              FStarC_Errors_Codes.Warning_UnexpectedCheckedFile ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___3)
          else ());
         (let uu___2 =
            (FStarC_Filepath.file_exists expected_cache_file) &&
              (FStarC_Filepath.paths_to_same_file path expected_cache_file) in
          if uu___2 then expected_cache_file else path))
    | FStar_Pervasives_Native.None ->
        ((let uu___2 = FStarC_Effect.op_Bang dbg_CheckedFiles in
          if uu___2
          then
            let uu___3 = FStarC_Filepath.basename cache_fn in
            FStarC_Format.print1 "find_file(%s) returned None\n" uu___3
          else ());
         (let uu___3 = FStarC_Options.should_be_already_cached mname in
          if uu___3
          then
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStarC_Format.fmt1
                    "Expected %s to be already checked but could not find it."
                    mname in
                FStarC_Errors_Msg.text uu___6 in
              [uu___5] in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Error_AlreadyCachedAssertionFailure ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___4)
          else ());
         FStarC_Find.prepend_cache_dir cache_fn) in
  let memo = FStarC_SMap.create (Prims.of_int (100)) in
  let memo1 f =
    fun x ->
      let uu___ = FStarC_SMap.try_find memo x in
      match uu___ with
      | FStar_Pervasives_Native.Some res -> res
      | FStar_Pervasives_Native.None ->
          let res = f x in (FStarC_SMap.add memo x res; res) in
  memo1 checked_file_and_exists_flag
let (parsing_data_of : deps -> Prims.string -> parsing_data) =
  fun deps1 ->
    fun fn ->
      let uu___ = FStarC_SMap.try_find deps1.parse_results fn in
      FStarC_Option.must uu___
let (file_of_dep_aux :
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name)
  =
  fun use_checked_file ->
    fun file_system_map ->
      fun all_cmd_line_files ->
        fun d ->
          let cmd_line_has_impl key =
            FStarC_Util.for_some
              (fun fn ->
                 (is_implementation fn) &&
                   (let uu___ = lowercase_module_name fn in key = uu___))
              all_cmd_line_files in
          let maybe_use_cache_of f =
            if use_checked_file then cache_file_name f else f in
          match d with
          | UseInterface key ->
              let uu___ = interface_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     FStarC_Format.fmt1
                       "Expected an interface for module %s, but couldn't find one"
                       key in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_MissingInterface ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___1)
               | FStar_Pervasives_Native.Some f -> f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu___ =
                (cmd_line_has_impl key) &&
                  (let uu___1 = FStarC_Options.dep () in
                   FStar_Pervasives_Native.uu___is_None uu___1) in
              if uu___
              then
                let uu___1 = FStarC_Options.expose_interfaces () in
                (if uu___1
                 then
                   let uu___2 =
                     let uu___3 =
                       implementation_of_internal file_system_map key in
                     FStarC_Option.must uu___3 in
                   maybe_use_cache_of uu___2
                 else
                   (let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              implementation_of_internal file_system_map key in
                            FStarC_Option.must uu___7 in
                          let uu___7 =
                            let uu___8 =
                              interface_of_internal file_system_map key in
                            FStarC_Option.must uu___8 in
                          FStarC_Format.fmt3
                            "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s."
                            key uu___6 uu___7 in
                        FStarC_Errors_Msg.text uu___5 in
                      let uu___5 =
                        let uu___6 =
                          FStarC_Errors_Msg.text
                            "If you really want this behavior add the option '--expose_interfaces'." in
                        [uu___6] in
                      uu___4 :: uu___5 in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Fatal_MissingExposeInterfacesOption
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___3)))
              else
                (let uu___2 =
                   let uu___3 = interface_of_internal file_system_map key in
                   FStarC_Option.must uu___3 in
                 maybe_use_cache_of uu___2)
          | PreferInterface key ->
              let uu___ = implementation_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     FStarC_Format.fmt1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_MissingImplementation ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___1)
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | UseImplementation key ->
              let uu___ = implementation_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     FStarC_Format.fmt1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_MissingImplementation ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___1)
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
          | FriendImplementation key ->
              let uu___ = implementation_of_internal file_system_map key in
              (match uu___ with
               | FStar_Pervasives_Native.None ->
                   let uu___1 =
                     FStarC_Format.fmt1
                       "Expected an implementation of module %s, but couldn't find one"
                       key in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_MissingImplementation ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___1)
               | FStar_Pervasives_Native.Some f -> maybe_use_cache_of f)
let (file_of_dep :
  files_for_module_name -> file_name Prims.list -> dependence -> file_name) =
  file_of_dep_aux false
let (dependences_of :
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list)
  =
  fun file_system_map ->
    fun deps1 ->
      fun all_cmd_line_files ->
        fun fn ->
          let uu___ = deps_try_find deps1 fn in
          match uu___ with
          | FStar_Pervasives_Native.None -> empty_dependences ()
          | FStar_Pervasives_Native.Some { edges = deps2; color = uu___1;_}
              ->
              let uu___2 =
                FStarC_List.map
                  (file_of_dep file_system_map all_cmd_line_files) deps2 in
              FStarC_List.filter (fun k -> k <> fn) uu___2
let (print_graph :
  FStarC_Util.out_channel ->
    Prims.string ->
      dependence_graph ->
        files_for_module_name -> file_name Prims.list -> unit)
  =
  fun outc ->
    fun fn ->
      fun graph ->
        fun file_system_map ->
          fun cmd_lined_files ->
            (let uu___1 =
               let uu___2 = FStarC_Options.silent () in
               Prims.op_Negation uu___2 in
             if uu___1
             then
               (FStarC_Format.print1
                  "A DOT-format graph has been dumped in the current directory as `%s`\n"
                  fn;
                FStarC_Format.print1
                  "With GraphViz installed, try: fdp -Tpng -odep.png %s\n" fn;
                FStarC_Format.print1
                  "Hint: cat %s | grep -v _ | grep -v prims\n" fn)
             else ());
            (let sb = FStarC_StringBuffer.create (Prims.of_int (10000)) in
             let pr str = let uu___1 = FStarC_StringBuffer.add str sb in () in
             pr "digraph {\n";
             (let uu___3 =
                let uu___4 = deps_keys graph in FStarC_List.unique uu___4 in
              FStarC_List.iter
                (fun k ->
                   let deps1 =
                     let uu___4 =
                       let uu___5 = deps_try_find graph k in
                       FStarC_Option.must uu___5 in
                     uu___4.edges in
                   FStarC_List.iter
                     (fun dep ->
                        let l = FStarC_Filepath.basename k in
                        let r =
                          let uu___4 =
                            file_of_dep file_system_map cmd_lined_files dep in
                          FStarC_Filepath.basename uu___4 in
                        let uu___4 =
                          let uu___5 =
                            FStarC_Options.should_be_already_cached
                              (module_name_of_dep dep) in
                          Prims.op_Negation uu___5 in
                        if uu___4
                        then
                          let uu___5 =
                            FStarC_Format.fmt2 "  \"%s\" -> \"%s\"\n" l r in
                          pr uu___5
                        else ()) deps1) uu___3);
             pr "}\n";
             (let uu___4 =
                let uu___5 = FStarC_StringBuffer.contents sb in [uu___5] in
              FStarC_Util.fprint outc "%s" uu___4))
let (safe_readdir_for_include : Prims.string -> Prims.string Prims.list) =
  fun d ->
    try (fun uu___ -> match () with | () -> FStarC_Filepath.readdir d) ()
    with | uu___ -> []
let (build_inclusion_candidates_list :
  unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu___ ->
    let include_directories = FStarC_Find.full_include_path () in
    let include_directories1 =
      FStarC_List.map FStarC_Filepath.normalize_file_path include_directories in
    let include_directories2 = FStarC_List.unique include_directories1 in
    let cwd =
      let uu___1 = FStarC_Util.getcwd () in
      FStarC_Filepath.normalize_file_path uu___1 in
    FStarC_List.concatMap
      (fun d ->
         let files = safe_readdir_for_include d in
         FStarC_List.filter_map
           (fun f ->
              let f1 = FStarC_Filepath.basename f in
              let uu___1 = check_and_strip_suffix f1 in
              FStarC_Option.map
                (fun longname ->
                   let full_path =
                     if d = cwd then f1 else FStarC_Filepath.join_paths d f1 in
                   (longname, full_path)) uu___1) files) include_directories2
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames ->
    let map = FStarC_SMap.create (Prims.of_int (41)) in
    let add_entry key =
      fun full_path ->
        let uu___ = FStarC_SMap.try_find map key in
        match uu___ with
        | FStar_Pervasives_Native.Some (intf, impl) ->
            let uu___1 = is_interface full_path in
            if uu___1
            then
              FStarC_SMap.add map key
                ((FStar_Pervasives_Native.Some full_path), impl)
            else
              FStarC_SMap.add map key
                (intf, (FStar_Pervasives_Native.Some full_path))
        | FStar_Pervasives_Native.None ->
            let uu___1 = is_interface full_path in
            if uu___1
            then
              FStarC_SMap.add map key
                ((FStar_Pervasives_Native.Some full_path),
                  FStar_Pervasives_Native.None)
            else
              FStarC_SMap.add map key
                (FStar_Pervasives_Native.None,
                  (FStar_Pervasives_Native.Some full_path)) in
    (let uu___1 = build_inclusion_candidates_list () in
     FStarC_List.iter
       (fun uu___2 ->
          match uu___2 with
          | (longname, full_path) ->
              add_entry (FStarC_String.lowercase longname) full_path) uu___1);
    FStarC_List.iter
      (fun f -> let uu___2 = lowercase_module_name f in add_entry uu___2 f)
      filenames;
    map
let (string_of_lid : FStarC_Ident.lident -> Prims.bool -> Prims.string) =
  fun l ->
    fun last ->
      let suffix =
        if last
        then
          let uu___ =
            let uu___1 = FStarC_Ident.ident_of_lid l in
            FStarC_Ident.string_of_id uu___1 in
          [uu___]
        else [] in
      let names =
        let uu___ =
          let uu___1 = FStarC_Ident.ns_of_lid l in
          FStarC_List.map (fun x -> FStarC_Ident.string_of_id x) uu___1 in
        FStarC_List.op_At uu___ suffix in
      FStarC_String.concat "." names
let (lowercase_join_longident :
  FStarC_Ident.lident -> Prims.bool -> Prims.string) =
  fun l ->
    fun last ->
      let uu___ = string_of_lid l last in FStarC_String.lowercase uu___
let (namespace_of_lid : FStarC_Ident.lident -> Prims.string) =
  fun l ->
    let uu___ =
      let uu___1 = FStarC_Ident.ns_of_lid l in
      FStarC_List.map FStarC_Ident.string_of_id uu___1 in
    FStarC_String.concat "_" uu___
let (check_module_declaration_against_filename :
  FStarC_Ident.lident -> Prims.string -> unit) =
  fun lid ->
    fun filename ->
      let k' = string_of_lid lid true in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Filepath.basename filename in
            check_and_strip_suffix uu___3 in
          FStarC_Option.must uu___2 in
        uu___1 <> k' in
      if uu___
      then
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = string_of_lid lid true in
              FStarC_Format.fmt2
                "The module declaration \"module %s\" found in file %s does not match its filename."
                uu___4 filename in
            FStarC_Errors_Msg.text uu___3 in
          let uu___3 =
            let uu___4 =
              FStarC_Errors_Msg.text
                "Dependencies will be incorrect and the module will not be verified." in
            [uu___4] in
          uu___2 :: uu___3 in
        FStarC_Errors.log_issue FStarC_Ident.hasrange_lident lid
          FStarC_Errors_Codes.Error_ModuleFileNameMismatch ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___1)
      else ()
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu___ -> false
let (dep_subsumed_by : dependence -> dependence -> Prims.bool) =
  fun d ->
    fun d' ->
      match (d, d') with
      | (PreferInterface l', FriendImplementation l) -> l = l'
      | uu___ -> d = d'
let (warned_about :
  intf_and_impl FStar_Pervasives_Native.option Prims.list FStarC_Effect.ref)
  = FStarC_Effect.mk_ref []
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool -> Prims.bool)
  =
  fun original_map ->
    fun working_map ->
      fun sprefix ->
        fun implicit_open ->
          let found = FStarC_Effect.mk_ref false in
          let sprefix1 = Prims.strcat sprefix "." in
          let suffix_exists mopt =
            match mopt with
            | FStar_Pervasives_Native.None -> false
            | FStar_Pervasives_Native.Some (intf, impl) ->
                (FStar_Pervasives_Native.uu___is_Some intf) ||
                  (FStar_Pervasives_Native.uu___is_Some impl) in
          FStarC_SMap.iter original_map
            (fun k ->
               fun uu___1 ->
                 if FStarC_Util.starts_with k sprefix1
                 then
                   let suffix =
                     FStarC_String.substring k
                       (FStarC_String.length sprefix1)
                       ((FStarC_String.length k) -
                          (FStarC_String.length sprefix1)) in
                   ((let suffix_filename =
                       FStarC_SMap.try_find original_map suffix in
                     let uu___3 =
                       (implicit_open && (suffix_exists suffix_filename)) &&
                         (let uu___4 =
                            let uu___5 = FStarC_Effect.op_Bang warned_about in
                            FStarC_List.mem suffix_filename uu___5 in
                          Prims.op_Negation uu___4) in
                     if uu___3
                     then
                       let str =
                         let uu___4 = FStarC_Option.must suffix_filename in
                         intf_and_impl_to_string uu___4 in
                       ((let uu___5 =
                           let uu___6 = FStarC_Effect.op_Bang warned_about in
                           suffix_filename :: uu___6 in
                         FStarC_Effect.op_Colon_Equals warned_about uu___5);
                        (let uu___5 =
                           let uu___6 =
                             let uu___7 = FStarC_Pprint.break_ Prims.int_one in
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Errors_Msg.text
                                   "Implicitly opening namespace" in
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 =
                                     FStarC_Pprint.doc_of_string sprefix1 in
                                   FStarC_Pprint.squotes uu___12 in
                                 let uu___12 =
                                   let uu___13 =
                                     FStarC_Errors_Msg.text "shadows module" in
                                   let uu___14 =
                                     let uu___15 =
                                       let uu___16 =
                                         FStarC_Pprint.doc_of_string suffix in
                                       FStarC_Pprint.squotes uu___16 in
                                     let uu___16 =
                                       let uu___17 =
                                         FStarC_Errors_Msg.text "in file" in
                                       let uu___18 =
                                         let uu___19 =
                                           let uu___20 =
                                             let uu___21 =
                                               FStarC_Pprint.doc_of_string
                                                 str in
                                             FStarC_Pprint.dquotes uu___21 in
                                           FStarC_Pprint.op_Hat_Hat uu___20
                                             FStarC_Pprint.dot in
                                         [uu___19] in
                                       uu___17 :: uu___18 in
                                     uu___15 :: uu___16 in
                                   uu___13 :: uu___14 in
                                 uu___11 :: uu___12 in
                               uu___9 :: uu___10 in
                             FStarC_Pprint.flow uu___7 uu___8 in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = FStarC_Errors_Msg.text "Rename" in
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 =
                                     FStarC_Pprint.doc_of_string str in
                                   FStarC_Pprint.dquotes uu___12 in
                                 let uu___12 =
                                   FStarC_Errors_Msg.text
                                     "to avoid conflicts." in
                                 FStarC_Pprint.op_Hat_Slash_Hat uu___11
                                   uu___12 in
                               FStarC_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                             [uu___8] in
                           uu___6 :: uu___7 in
                         FStarC_Errors.log_issue0
                           FStarC_Errors_Codes.Warning_UnexpectedFile ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_list_doc)
                           (Obj.magic uu___5)))
                     else ());
                    (let filename =
                       let uu___3 = FStarC_SMap.try_find original_map k in
                       FStarC_Option.must uu___3 in
                     FStarC_SMap.add working_map suffix filename;
                     FStarC_Effect.op_Colon_Equals found true))
                 else ());
          FStarC_Effect.op_Bang found
let (prelude : (open_kind * FStarC_Ident.lid) Prims.list) =
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Ident.lid_of_str "FStar.Prelude" in
      (Open_module, uu___2) in
    [uu___1] in
  (Open_namespace, FStarC_Parser_Const.fstar_ns_lid) :: uu___
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
        (parsing_data * dependence Prims.list * Prims.bool * dependence
          Prims.list))
  =
  fun original_map ->
    fun filename ->
      fun get_parsing_data_from_cache ->
        let from_parsing_data pd =
          fun original_map1 ->
            fun filename1 ->
              let deps1 = FStarC_Effect.mk_ref [] in
              let has_inline_for_extraction = FStarC_Effect.mk_ref false in
              let mname = lowercase_module_name filename1 in
              let mo_roots =
                let uu___ =
                  (is_interface filename1) &&
                    (has_implementation original_map1 mname) in
                if uu___ then [UseImplementation mname] else [] in
              let auto_open =
                if pd.no_prelude
                then []
                else
                  (let uu___1 =
                     FStarC_List.map
                       (fun uu___2 ->
                          match uu___2 with | (k, l) -> P_open (false, l))
                       prelude in
                   let uu___2 =
                     let uu___3 = namespace_of_module mname in
                     match uu___3 with
                     | FStar_Pervasives_Native.None -> []
                     | FStar_Pervasives_Native.Some ns ->
                         [P_implicit_open_module_or_namespace
                            (Open_namespace, ns)] in
                   FStarC_List.op_At uu___1 uu___2) in
              let working_map = FStarC_SMap.copy original_map1 in
              let set_interface_inlining uu___ =
                let uu___1 = is_interface filename1 in
                if uu___1
                then
                  FStarC_Effect.op_Colon_Equals has_inline_for_extraction
                    true
                else () in
              let add_dep deps2 =
                fun d ->
                  let uu___ =
                    let uu___1 =
                      let uu___2 = FStarC_Effect.op_Bang deps2 in
                      FStarC_List.existsML (dep_subsumed_by d) uu___2 in
                    Prims.op_Negation uu___1 in
                  if uu___
                  then
                    let uu___1 =
                      let uu___2 = FStarC_Effect.op_Bang deps2 in d :: uu___2 in
                    FStarC_Effect.op_Colon_Equals deps2 uu___1
                  else () in
              let dep_edge module_name1 =
                fun is_friend ->
                  if is_friend
                  then FriendImplementation module_name1
                  else PreferInterface module_name1 in
              let add_dependence_edge original_or_working_map =
                fun lid ->
                  fun is_friend ->
                    let key = lowercase_join_longident lid true in
                    let uu___ =
                      resolve_module_name original_or_working_map key in
                    match uu___ with
                    | FStar_Pervasives_Native.Some module_name1 ->
                        (add_dep deps1 (dep_edge module_name1 is_friend);
                         true)
                    | uu___1 -> false in
              let record_open_module let_open =
                fun lid ->
                  let uu___ =
                    (let_open && (add_dependence_edge working_map lid false))
                      ||
                      ((Prims.op_Negation let_open) &&
                         (add_dependence_edge original_map1 lid false)) in
                  if uu___
                  then true
                  else
                    (if let_open
                     then
                       (let uu___3 =
                          let uu___4 = string_of_lid lid true in
                          FStarC_Format.fmt1 "Module not found: %s" uu___4 in
                        FStarC_Errors.log_issue FStarC_Ident.hasrange_lident
                          lid
                          FStarC_Errors_Codes.Warning_ModuleOrFileNotFoundWarning
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___3))
                     else ();
                     false) in
              let record_open_namespace lid =
                fun implicit_open ->
                  let key = lowercase_join_longident lid true in
                  let r =
                    enter_namespace original_map1 working_map key
                      implicit_open in
                  if
                    (Prims.op_Negation r) &&
                      (Prims.op_Negation implicit_open)
                  then
                    let uu___ =
                      let uu___1 = string_of_lid lid true in
                      FStarC_Format.fmt1
                        "No modules in namespace %s and no file with that name either"
                        uu___1 in
                    FStarC_Errors.log_issue FStarC_Ident.hasrange_lident lid
                      FStarC_Errors_Codes.Warning_ModuleOrFileNotFoundWarning
                      ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                      (Obj.magic uu___)
                  else () in
              let record_open let_open =
                fun lid ->
                  let uu___ = record_open_module let_open lid in
                  if uu___
                  then ()
                  else
                    if Prims.op_Negation let_open
                    then record_open_namespace lid false
                    else () in
              let record_implicit_open_module_or_namespace uu___ =
                match uu___ with
                | (lid, kind) ->
                    (match kind with
                     | Open_namespace -> record_open_namespace lid true
                     | Open_module ->
                         let uu___1 = record_open_module false lid in ()) in
              let record_module_alias ident =
                fun lid ->
                  let key =
                    let uu___ = FStarC_Ident.string_of_id ident in
                    FStarC_String.lowercase uu___ in
                  let alias = lowercase_join_longident lid true in
                  let uu___ = FStarC_SMap.try_find original_map1 alias in
                  match uu___ with
                  | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                      (FStarC_SMap.add working_map key deps_of_aliased_module;
                       (let uu___3 =
                          let uu___4 = lowercase_join_longident lid true in
                          dep_edge uu___4 false in
                        add_dep deps1 uu___3);
                       true)
                  | FStar_Pervasives_Native.None ->
                      ((let uu___2 =
                          FStarC_Format.fmt1
                            "module not found in search path: %s" alias in
                        FStarC_Errors.log_issue FStarC_Ident.hasrange_lident
                          lid
                          FStarC_Errors_Codes.Warning_ModuleOrFileNotFoundWarning
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___2));
                       false) in
              let add_dep_on_module module_name1 =
                fun is_friend ->
                  let uu___ =
                    add_dependence_edge working_map module_name1 is_friend in
                  if uu___
                  then ()
                  else
                    (let uu___2 = FStarC_Effect.op_Bang dbg in
                     if uu___2
                     then
                       let uu___3 =
                         let uu___4 =
                           FStarC_Class_Show.show
                             FStarC_Ident.showable_lident module_name1 in
                         FStarC_Format.fmt1 "Unbound module reference %s"
                           uu___4 in
                       FStarC_Errors.log_issue FStarC_Ident.hasrange_lident
                         module_name1
                         FStarC_Errors_Codes.Warning_UnboundModuleReference
                         ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___3)
                     else ()) in
              let record_lid lid =
                let uu___ = FStarC_Ident.ns_of_lid lid in
                match uu___ with
                | [] -> ()
                | ns ->
                    let module_name1 = FStarC_Ident.lid_of_ids ns in
                    add_dep_on_module module_name1 false in
              let begin_module lid =
                let uu___ =
                  let uu___1 =
                    let uu___2 = FStarC_Ident.ns_of_lid lid in
                    FStarC_List.length uu___2 in
                  uu___1 > Prims.int_zero in
                if uu___
                then
                  let uu___1 =
                    let uu___2 = namespace_of_lid lid in
                    enter_namespace original_map1 working_map uu___2 in
                  ()
                else () in
              FStarC_List.iter
                (fun elt ->
                   match elt with
                   | P_begin_module lid -> begin_module lid
                   | P_open (b, lid) -> record_open b lid
                   | P_implicit_open_module_or_namespace (k, lid) ->
                       record_implicit_open_module_or_namespace (lid, k)
                   | P_dep (b, lid) -> add_dep_on_module lid b
                   | P_alias (id, lid) ->
                       let uu___1 = record_module_alias id lid in ()
                   | P_lid lid -> record_lid lid
                   | P_inline_for_extraction -> set_interface_inlining ())
                (FStarC_List.op_At auto_open pd.elts);
              (let uu___1 = FStarC_Effect.op_Bang deps1 in
               let uu___2 = FStarC_Effect.op_Bang has_inline_for_extraction in
               (uu___1, uu___2, mo_roots)) in
        let data_from_cache = get_parsing_data_from_cache filename in
        if FStar_Pervasives_Native.uu___is_Some data_from_cache
        then
          let uu___ =
            let uu___1 = FStarC_Option.must data_from_cache in
            from_parsing_data uu___1 original_map filename in
          match uu___ with
          | (deps1, has_inline_for_extraction, mo_roots) ->
              ((let uu___2 = FStarC_Effect.op_Bang dbg in
                if uu___2
                then
                  let uu___3 =
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_list showable_dependence) deps1 in
                  FStarC_Format.print2
                    "Reading the parsing data for %s from its checked file .. found %s\n"
                    filename uu___3
                else ());
               (let uu___2 = FStarC_Option.must data_from_cache in
                (uu___2, deps1, has_inline_for_extraction, mo_roots)))
        else
          (let num_of_toplevelmods = FStarC_Effect.mk_ref Prims.int_zero in
           let pd = FStarC_Effect.mk_ref empty_parsing_data in
           let add_to_parsing_data elt =
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Effect.op_Bang pd in uu___4.elts in
                 FStarC_List.existsML (fun e -> parsing_data_elt_eq e elt)
                   uu___3 in
               Prims.op_Negation uu___2 in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = FStarC_Effect.op_Bang pd in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = FStarC_Effect.op_Bang pd in uu___6.elts in
                   elt :: uu___5 in
                 { elts = uu___4; no_prelude = (uu___3.no_prelude) } in
               FStarC_Effect.op_Colon_Equals pd uu___2
             else () in
           let set_no_prelude b =
             let uu___1 =
               let uu___2 = FStarC_Effect.op_Bang pd in
               { elts = (uu___2.elts); no_prelude = b } in
             FStarC_Effect.op_Colon_Equals pd uu___1 in
           let rec collect_module uu___1 =
             match uu___1 with
             | FStarC_Parser_AST.Module
                 { FStarC_Parser_AST.no_prelude = no_prelude;
                   FStarC_Parser_AST.mname = mname;
                   FStarC_Parser_AST.decls = decls;_}
                 ->
                 (set_no_prelude no_prelude;
                  check_module_declaration_against_filename mname filename;
                  add_to_parsing_data (P_begin_module mname);
                  collect_decls decls)
             | FStarC_Parser_AST.Interface
                 { FStarC_Parser_AST.no_prelude1 = no_prelude;
                   FStarC_Parser_AST.mname1 = mname;
                   FStarC_Parser_AST.decls1 = decls;
                   FStarC_Parser_AST.admitted = uu___2;_}
                 ->
                 (set_no_prelude no_prelude;
                  check_module_declaration_against_filename mname filename;
                  add_to_parsing_data (P_begin_module mname);
                  collect_decls decls)
           and collect_decls decls =
             FStarC_List.iter
               (fun x ->
                  collect_decl x.FStarC_Parser_AST.d;
                  FStarC_List.iter collect_term x.FStarC_Parser_AST.attrs;
                  if
                    FStarC_List.contains
                      FStarC_Parser_AST.Inline_for_extraction
                      x.FStarC_Parser_AST.quals
                  then add_to_parsing_data P_inline_for_extraction
                  else ()) decls
           and collect_decl d =
             match d with
             | FStarC_Parser_AST.Include (lid, uu___1) ->
                 add_to_parsing_data (P_open (false, lid))
             | FStarC_Parser_AST.Open (lid, uu___1) ->
                 add_to_parsing_data (P_open (false, lid))
             | FStarC_Parser_AST.Friend lid ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = lowercase_join_longident lid true in
                       FStarC_Ident.lid_of_str uu___4 in
                     (true, uu___3) in
                   P_dep uu___2 in
                 add_to_parsing_data uu___1
             | FStarC_Parser_AST.ModuleAbbrev (ident, lid) ->
                 add_to_parsing_data (P_alias (ident, lid))
             | FStarC_Parser_AST.TopLevelLet (uu___1, patterms) ->
                 FStarC_List.iter
                   (fun uu___2 ->
                      match uu___2 with
                      | (pat, t) -> (collect_pattern pat; collect_term t))
                   patterms
             | FStarC_Parser_AST.Splice (uu___1, uu___2, t) -> collect_term t
             | FStarC_Parser_AST.Assume (uu___1, t) -> collect_term t
             | FStarC_Parser_AST.SubEffect
                 { FStarC_Parser_AST.msource = uu___1;
                   FStarC_Parser_AST.mdest = uu___2;
                   FStarC_Parser_AST.lift_op =
                     FStarC_Parser_AST.NonReifiableLift t;
                   FStarC_Parser_AST.braced = uu___3;_}
                 -> collect_term t
             | FStarC_Parser_AST.SubEffect
                 { FStarC_Parser_AST.msource = uu___1;
                   FStarC_Parser_AST.mdest = uu___2;
                   FStarC_Parser_AST.lift_op = FStarC_Parser_AST.LiftForFree
                     t;
                   FStarC_Parser_AST.braced = uu___3;_}
                 -> collect_term t
             | FStarC_Parser_AST.Val (uu___1, t) -> collect_term t
             | FStarC_Parser_AST.SubEffect
                 { FStarC_Parser_AST.msource = uu___1;
                   FStarC_Parser_AST.mdest = uu___2;
                   FStarC_Parser_AST.lift_op =
                     FStarC_Parser_AST.ReifiableLift (t0, t1);
                   FStarC_Parser_AST.braced = uu___3;_}
                 -> (collect_term t0; collect_term t1)
             | FStarC_Parser_AST.Tycon (uu___1, tc, ts) ->
                 (if tc
                  then
                    add_to_parsing_data
                      (P_lid FStarC_Parser_Const.tcclass_lid)
                  else ();
                  FStarC_List.iter collect_tycon ts)
             | FStarC_Parser_AST.Exception (uu___1, t) ->
                 FStarC_Option.iter collect_term t
             | FStarC_Parser_AST.NewEffect ed -> collect_effect_decl ed
             | FStarC_Parser_AST.LayeredEffect ed -> collect_effect_decl ed
             | FStarC_Parser_AST.Polymonadic_bind (uu___1, uu___2, uu___3, t)
                 -> collect_term t
             | FStarC_Parser_AST.Polymonadic_subcomp (uu___1, uu___2, t) ->
                 collect_term t
             | FStarC_Parser_AST.DeclToBeDesugared tbs ->
                 tbs.FStarC_Parser_AST.dep_scan
                   {
                     FStarC_Parser_AST.scan_term = collect_term;
                     FStarC_Parser_AST.scan_binder = collect_binder;
                     FStarC_Parser_AST.scan_pattern = collect_pattern;
                     FStarC_Parser_AST.add_lident =
                       (fun lid -> add_to_parsing_data (P_lid lid));
                     FStarC_Parser_AST.add_open =
                       (fun lid -> add_to_parsing_data (P_open (true, lid)))
                   } tbs.FStarC_Parser_AST.blob
             | FStarC_Parser_AST.UseLangDecls uu___1 -> ()
             | FStarC_Parser_AST.Pragma uu___1 -> ()
             | FStarC_Parser_AST.DeclSyntaxExtension uu___1 -> ()
             | FStarC_Parser_AST.Unparseable -> ()
             | FStarC_Parser_AST.TopLevelModule lid ->
                 (FStarC_Util.incr num_of_toplevelmods;
                  (let uu___2 =
                     let uu___3 = FStarC_Effect.op_Bang num_of_toplevelmods in
                     uu___3 > Prims.int_one in
                   if uu___2
                   then
                     let uu___3 =
                       let uu___4 = string_of_lid lid true in
                       FStarC_Format.fmt1
                         "Automatic dependency analysis demands one module per file (module %s not supported)"
                         uu___4 in
                     FStarC_Errors.raise_error FStarC_Ident.hasrange_lident
                       lid FStarC_Errors_Codes.Fatal_OneModulePerFile ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___3)
                   else ()))
           and collect_tycon uu___1 =
             match uu___1 with
             | FStarC_Parser_AST.TyconAbstract (uu___2, binders, k) ->
                 (collect_binders binders; FStarC_Option.iter collect_term k)
             | FStarC_Parser_AST.TyconAbbrev (uu___2, binders, k, t) ->
                 (collect_binders binders;
                  FStarC_Option.iter collect_term k;
                  collect_term t)
             | FStarC_Parser_AST.TyconRecord
                 (uu___2, binders, k, uu___3, identterms) ->
                 (collect_binders binders;
                  FStarC_Option.iter collect_term k;
                  collect_tycon_record identterms)
             | FStarC_Parser_AST.TyconVariant
                 (uu___2, binders, k, identterms) ->
                 (collect_binders binders;
                  FStarC_Option.iter collect_term k;
                  (let uu___5 =
                     FStarC_List.filter_map
                       FStar_Pervasives_Native.__proj__Mktuple3__item___2
                       identterms in
                   FStarC_List.iter
                     (fun uu___6 ->
                        match uu___6 with
                        | FStarC_Parser_AST.VpOfNotation t -> collect_term t
                        | FStarC_Parser_AST.VpArbitrary t -> collect_term t
                        | FStarC_Parser_AST.VpRecord (record, t) ->
                            (collect_tycon_record record;
                             FStarC_Option.iter collect_term t)) uu___5))
           and collect_tycon_record r =
             FStarC_List.iter
               (fun uu___1 ->
                  match uu___1 with
                  | (uu___2, aq, attrs, t) ->
                      (collect_aqual aq;
                       FStarC_List.iter collect_term attrs;
                       collect_term t)) r
           and collect_effect_decl uu___1 =
             match uu___1 with
             | FStarC_Parser_AST.DefineEffect (uu___2, binders, t, decls) ->
                 (collect_binders binders;
                  collect_term t;
                  collect_decls decls)
             | FStarC_Parser_AST.RedefineEffect (uu___2, binders, t) ->
                 (collect_binders binders; collect_term t)
           and collect_binders binders =
             FStarC_List.iter collect_binder binders
           and collect_binder b =
             collect_aqual b.FStarC_Parser_AST.aqual;
             FStarC_List.iter collect_term b.FStarC_Parser_AST.battributes;
             (match b with
              | {
                  FStarC_Parser_AST.b = FStarC_Parser_AST.Annotated
                    (uu___3, t);
                  FStarC_Parser_AST.brange = uu___4;
                  FStarC_Parser_AST.blevel = uu___5;
                  FStarC_Parser_AST.aqual = uu___6;
                  FStarC_Parser_AST.battributes = uu___7;_} -> collect_term t
              | {
                  FStarC_Parser_AST.b = FStarC_Parser_AST.TAnnotated
                    (uu___3, t);
                  FStarC_Parser_AST.brange = uu___4;
                  FStarC_Parser_AST.blevel = uu___5;
                  FStarC_Parser_AST.aqual = uu___6;
                  FStarC_Parser_AST.battributes = uu___7;_} -> collect_term t
              | { FStarC_Parser_AST.b = FStarC_Parser_AST.NoName t;
                  FStarC_Parser_AST.brange = uu___3;
                  FStarC_Parser_AST.blevel = uu___4;
                  FStarC_Parser_AST.aqual = uu___5;
                  FStarC_Parser_AST.battributes = uu___6;_} -> collect_term t
              | uu___3 -> ())
           and collect_aqual uu___1 =
             match uu___1 with
             | FStar_Pervasives_Native.Some (FStarC_Parser_AST.Meta t) ->
                 collect_term t
             | FStar_Pervasives_Native.Some (FStarC_Parser_AST.TypeClassArg)
                 ->
                 add_to_parsing_data
                   (P_lid FStarC_Parser_Const.tcresolve_lid)
             | uu___2 -> ()
           and collect_term t = collect_term' t.FStarC_Parser_AST.tm
           and collect_constant uu___1 =
             match uu___1 with
             | FStarC_Const.Const_int
                 (uu___2, FStar_Pervasives_Native.Some
                  (FStarC_Const.Unsigned, FStarC_Const.Sizet))
                 ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = FStarC_Ident.lid_of_str "fstar.sizeT" in
                     (false, uu___5) in
                   P_dep uu___4 in
                 add_to_parsing_data uu___3
             | FStarC_Const.Const_int
                 (uu___2, FStar_Pervasives_Native.Some (signedness, width))
                 ->
                 let u =
                   match signedness with
                   | FStarC_Const.Unsigned -> "u"
                   | FStarC_Const.Signed -> "" in
                 let w =
                   match width with
                   | FStarC_Const.Int8 -> "8"
                   | FStarC_Const.Int16 -> "16"
                   | FStarC_Const.Int32 -> "32"
                   | FStarC_Const.Int64 -> "64" in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Format.fmt2 "fstar.%sint%s" u w in
                       FStarC_Ident.lid_of_str uu___6 in
                     (false, uu___5) in
                   P_dep uu___4 in
                 add_to_parsing_data uu___3
             | FStarC_Const.Const_char uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = FStarC_Ident.lid_of_str "fstar.char" in
                     (false, uu___5) in
                   P_dep uu___4 in
                 add_to_parsing_data uu___3
             | FStarC_Const.Const_range_of ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Ident.lid_of_str "fstar.range" in
                     (false, uu___4) in
                   P_dep uu___3 in
                 add_to_parsing_data uu___2
             | FStarC_Const.Const_set_range_of ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Ident.lid_of_str "fstar.range" in
                     (false, uu___4) in
                   P_dep uu___3 in
                 add_to_parsing_data uu___2
             | FStarC_Const.Const_real uu___2 ->
                 let mm = maybe_module_name_of_file filename in
                 if mm <> (FStar_Pervasives_Native.Some "FStar.Real")
                 then
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Ident.lid_of_str "fstar.real" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3
                 else ()
             | uu___2 -> ()
           and collect_term' uu___1 =
             match uu___1 with
             | FStarC_Parser_AST.Wild -> ()
             | FStarC_Parser_AST.Const c -> collect_constant c
             | FStarC_Parser_AST.Op (uu___2, ts) ->
                 FStarC_List.iter collect_term ts
             | FStarC_Parser_AST.Tvar uu___2 -> ()
             | FStarC_Parser_AST.Uvar uu___2 -> ()
             | FStarC_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
             | FStarC_Parser_AST.Projector (lid, uu___2) ->
                 add_to_parsing_data (P_lid lid)
             | FStarC_Parser_AST.Discrim lid ->
                 add_to_parsing_data (P_lid lid)
             | FStarC_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
             | FStarC_Parser_AST.Construct (lid, termimps) ->
                 (add_to_parsing_data (P_lid lid);
                  FStarC_List.iter
                    (fun uu___3 ->
                       match uu___3 with | (t, uu___4) -> collect_term t)
                    termimps)
             | FStarC_Parser_AST.Function (branches, uu___2) ->
                 collect_branches branches
             | FStarC_Parser_AST.Abs (pats, t) ->
                 (collect_patterns pats; collect_term t)
             | FStarC_Parser_AST.App (t1, t2, uu___2) ->
                 (collect_term t1; collect_term t2)
             | FStarC_Parser_AST.Let (uu___2, patterms, t) ->
                 (FStarC_List.iter
                    (fun uu___4 ->
                       match uu___4 with
                       | (attrs_opt, (pat, t1)) ->
                           ((let uu___6 =
                               FStarC_Option.map
                                 (FStarC_List.iter collect_term) attrs_opt in
                             ());
                            collect_pattern pat;
                            collect_term t1)) patterms;
                  collect_term t)
             | FStarC_Parser_AST.LetOperator (lets, body) ->
                 (FStarC_List.iter
                    (fun uu___3 ->
                       match uu___3 with
                       | (ident, pat, def) ->
                           (collect_pattern pat; collect_term def)) lets;
                  collect_term body)
             | FStarC_Parser_AST.LetOpen (lid, t) ->
                 (add_to_parsing_data (P_open (true, lid)); collect_term t)
             | FStarC_Parser_AST.LetOpenRecord (r, rty, e) ->
                 (collect_term r; collect_term rty; collect_term e)
             | FStarC_Parser_AST.Bind (uu___2, t1, t2) ->
                 (collect_term t1; collect_term t2)
             | FStarC_Parser_AST.Seq (t1, t2) ->
                 (collect_term t1; collect_term t2)
             | FStarC_Parser_AST.If (t1, uu___2, ret_opt, t2, t3) ->
                 (collect_term t1;
                  (match ret_opt with
                   | FStar_Pervasives_Native.None -> ()
                   | FStar_Pervasives_Native.Some (uu___5, ret, uu___6) ->
                       collect_term ret);
                  collect_term t2;
                  collect_term t3)
             | FStarC_Parser_AST.Match (t, uu___2, ret_opt, bs) ->
                 (collect_term t;
                  (match ret_opt with
                   | FStar_Pervasives_Native.None -> ()
                   | FStar_Pervasives_Native.Some (uu___5, ret, uu___6) ->
                       collect_term ret);
                  collect_branches bs)
             | FStarC_Parser_AST.TryWith (t, bs) ->
                 (collect_term t; collect_branches bs)
             | FStarC_Parser_AST.Ascribed
                 (t1, t2, FStar_Pervasives_Native.None, uu___2) ->
                 (collect_term t1; collect_term t2)
             | FStarC_Parser_AST.Ascribed
                 (t1, t2, FStar_Pervasives_Native.Some tac, uu___2) ->
                 (collect_term t1; collect_term t2; collect_term tac)
             | FStarC_Parser_AST.Record (t, idterms) ->
                 (FStarC_Option.iter collect_term t;
                  FStarC_List.iter
                    (fun uu___3 ->
                       match uu___3 with
                       | (fn, t1) -> (collect_fieldname fn; collect_term t1))
                    idterms)
             | FStarC_Parser_AST.Project (t, f) ->
                 (collect_term t; collect_fieldname f)
             | FStarC_Parser_AST.Product (binders, t) ->
                 (collect_binders binders; collect_term t)
             | FStarC_Parser_AST.Sum (binders, t) ->
                 (FStarC_List.iter
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Pervasives.Inl b -> collect_binder b
                       | FStar_Pervasives.Inr t1 -> collect_term t1) binders;
                  collect_term t)
             | FStarC_Parser_AST.QForall (binders, (uu___2, ts), t) ->
                 (collect_binders binders;
                  FStarC_List.iter (FStarC_List.iter collect_term) ts;
                  collect_term t)
             | FStarC_Parser_AST.QExists (binders, (uu___2, ts), t) ->
                 (collect_binders binders;
                  FStarC_List.iter (FStarC_List.iter collect_term) ts;
                  collect_term t)
             | FStarC_Parser_AST.QuantOp (uu___2, binders, (uu___3, ts), t)
                 ->
                 (collect_binders binders;
                  FStarC_List.iter (FStarC_List.iter collect_term) ts;
                  collect_term t)
             | FStarC_Parser_AST.Refine (binder, t) ->
                 (collect_binder binder; collect_term t)
             | FStarC_Parser_AST.NamedTyp (uu___2, t) -> collect_term t
             | FStarC_Parser_AST.Paren t -> collect_term t
             | FStarC_Parser_AST.Requires (t, uu___2) -> collect_term t
             | FStarC_Parser_AST.Ensures (t, uu___2) -> collect_term t
             | FStarC_Parser_AST.Labeled (t, uu___2, uu___3) ->
                 collect_term t
             | FStarC_Parser_AST.LexList l -> FStarC_List.iter collect_term l
             | FStarC_Parser_AST.WFOrder (t1, t2) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.WellFounded" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term t1;
                  collect_term t2)
             | FStarC_Parser_AST.Decreases (t, uu___2) -> collect_term t
             | FStarC_Parser_AST.Quote (t, uu___2) -> collect_term t
             | FStarC_Parser_AST.Antiquote t -> collect_term t
             | FStarC_Parser_AST.VQuote t -> collect_term t
             | FStarC_Parser_AST.Attributes cattributes ->
                 FStarC_List.iter collect_term cattributes
             | FStarC_Parser_AST.CalcProof (rel, init, steps) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Ident.lid_of_str "FStar.Calc" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term rel;
                  collect_term init;
                  FStarC_List.iter
                    (fun uu___5 ->
                       match uu___5 with
                       | FStarC_Parser_AST.CalcStep (rel1, just, next) ->
                           (collect_term rel1;
                            collect_term just;
                            collect_term next)) steps)
             | FStarC_Parser_AST.IntroForall (bs, p, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_binders bs;
                  collect_term p;
                  collect_term e)
             | FStarC_Parser_AST.IntroExists (bs, t, vs, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_binders bs;
                  collect_term t;
                  FStarC_List.iter collect_term vs;
                  collect_term e)
             | FStarC_Parser_AST.IntroImplies (p, q, x, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term p;
                  collect_term q;
                  collect_binder x;
                  collect_term e)
             | FStarC_Parser_AST.IntroOr (b, p, q, r) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term p;
                  collect_term q;
                  collect_term r)
             | FStarC_Parser_AST.IntroAnd (p, q, r, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term p;
                  collect_term q;
                  collect_term r;
                  collect_term e)
             | FStarC_Parser_AST.ElimForall (bs, p, vs) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_binders bs;
                  collect_term p;
                  FStarC_List.iter collect_term vs)
             | FStarC_Parser_AST.ElimExists (bs, p, q, b, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_binders bs;
                  collect_term p;
                  collect_term q;
                  collect_binder b;
                  collect_term e)
             | FStarC_Parser_AST.ElimImplies (p, q, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term p;
                  collect_term q;
                  collect_term e)
             | FStarC_Parser_AST.ElimAnd (p, q, r, x, y, e) ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term p;
                  collect_term q;
                  collect_term r;
                  collect_binder x;
                  collect_binder y;
                  collect_term e)
             | FStarC_Parser_AST.ElimOr (p, q, r, x, e, y, e') ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  collect_term p;
                  collect_term q;
                  collect_term r;
                  collect_binder x;
                  collect_binder y;
                  collect_term e;
                  collect_term e')
             | FStarC_Parser_AST.ListLiteral ts ->
                 FStarC_List.iter collect_term ts
             | FStarC_Parser_AST.SeqLiteral ts ->
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Ident.lid_of_str "FStar.Seq.Base" in
                       (false, uu___5) in
                     P_dep uu___4 in
                   add_to_parsing_data uu___3);
                  FStarC_List.iter collect_term ts)
           and collect_patterns ps = FStarC_List.iter collect_pattern ps
           and collect_pattern p = collect_pattern' p.FStarC_Parser_AST.pat
           and collect_pattern' uu___1 =
             match uu___1 with
             | FStarC_Parser_AST.PatVar (uu___2, aqual, attrs) ->
                 (collect_aqual aqual; FStarC_List.iter collect_term attrs)
             | FStarC_Parser_AST.PatTvar (uu___2, aqual, attrs) ->
                 (collect_aqual aqual; FStarC_List.iter collect_term attrs)
             | FStarC_Parser_AST.PatWild (aqual, attrs) ->
                 (collect_aqual aqual; FStarC_List.iter collect_term attrs)
             | FStarC_Parser_AST.PatRest -> ()
             | FStarC_Parser_AST.PatOp uu___2 -> ()
             | FStarC_Parser_AST.PatConst uu___2 -> ()
             | FStarC_Parser_AST.PatVQuote t -> collect_term t
             | FStarC_Parser_AST.PatApp (p, ps) ->
                 (collect_pattern p; collect_patterns ps)
             | FStarC_Parser_AST.PatName lid ->
                 add_to_parsing_data (P_lid lid)
             | FStarC_Parser_AST.PatList ps -> collect_patterns ps
             | FStarC_Parser_AST.PatOr ps -> collect_patterns ps
             | FStarC_Parser_AST.PatTuple (ps, uu___2) -> collect_patterns ps
             | FStarC_Parser_AST.PatRecord lidpats ->
                 FStarC_List.iter
                   (fun uu___2 ->
                      match uu___2 with | (uu___3, p) -> collect_pattern p)
                   lidpats
             | FStarC_Parser_AST.PatAscribed
                 (p, (t, FStar_Pervasives_Native.None)) ->
                 (collect_pattern p; collect_term t)
             | FStarC_Parser_AST.PatAscribed
                 (p, (t, FStar_Pervasives_Native.Some tac)) ->
                 (collect_pattern p; collect_term t; collect_term tac)
           and collect_branches bs = FStarC_List.iter collect_branch bs
           and collect_branch uu___1 =
             match uu___1 with
             | (pat, t1, t2) ->
                 (collect_pattern pat;
                  FStarC_Option.iter collect_term t1;
                  collect_term t2)
           and collect_fieldname fn =
             let uu___1 = let uu___2 = FStarC_Ident.nsstr fn in uu___2 <> "" in
             if uu___1
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = FStarC_Ident.ns_of_lid fn in
                     FStarC_Ident.lid_of_ids uu___5 in
                   (false, uu___4) in
                 P_dep uu___3 in
               add_to_parsing_data uu___2
             else () in
           let uu___1 = FStarC_Parser_Driver.parse_file filename in
           match uu___1 with
           | (ast, uu___2) ->
               (collect_module ast;
                (let pd1 = FStarC_Effect.op_Bang pd in
                 let pd2 =
                   {
                     elts = (FStarC_List.rev pd1.elts);
                     no_prelude = (pd1.no_prelude)
                   } in
                 let uu___4 = from_parsing_data pd2 original_map filename in
                 match uu___4 with
                 | (deps1, has_inline_for_extraction, mo_roots) ->
                     (pd2, deps1, has_inline_for_extraction, mo_roots))))
let (collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool) FStarC_SMap.t
    FStarC_Effect.ref)
  =
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let (set_collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool) FStarC_SMap.t
    -> unit)
  = fun cache -> FStarC_Effect.op_Colon_Equals collect_one_cache cache
let (dep_graph_copy : dependence_graph -> dependence_graph) =
  fun dep_graph ->
    let uu___ = dep_graph in
    match uu___ with
    | Deps g -> let uu___1 = FStarC_SMap.copy g in Deps uu___1
let (widen_deps :
  module_name Prims.list ->
    dependence_graph ->
      files_for_module_name -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun friends1 ->
    fun dep_graph ->
      fun file_system_map ->
        fun widened ->
          let widened1 = FStarC_Effect.mk_ref widened in
          let uu___ = dep_graph in
          match uu___ with
          | Deps dg ->
              let uu___1 = deps_empty () in
              (match uu___1 with
               | Deps dg' ->
                   let widen_one deps1 =
                     FStarC_List.map
                       (fun d ->
                          match d with
                          | PreferInterface m when
                              (FStarC_List.contains m friends1) &&
                                (has_implementation file_system_map m)
                              ->
                              (FStarC_Effect.op_Colon_Equals widened1 true;
                               FriendImplementation m)
                          | uu___2 -> d) deps1 in
                   (FStarC_SMap.fold dg
                      (fun filename ->
                         fun dep_node1 ->
                           fun uu___3 ->
                             let uu___4 =
                               let uu___5 = widen_one dep_node1.edges in
                               { edges = uu___5; color = White } in
                             FStarC_SMap.add dg' filename uu___4) ();
                    (let uu___3 = FStarC_Effect.op_Bang widened1 in
                     (uu___3, (Deps dg')))))
let (topological_dependences_of' :
  files_for_module_name ->
    dependence_graph ->
      Prims.string Prims.list ->
        file_name Prims.list ->
          Prims.bool -> (file_name Prims.list * Prims.bool))
  =
  fun file_system_map ->
    fun dep_graph ->
      fun interfaces_needing_inlining ->
        fun root_files ->
          fun widened ->
            let rec all_friend_deps_1 dep_graph1 =
              fun cycle ->
                fun uu___ ->
                  fun filename ->
                    match uu___ with
                    | (all_friends, all_files) ->
                        let dep_node1 =
                          let uu___1 = deps_try_find dep_graph1 filename in
                          FStarC_Option.must uu___1 in
                        (match dep_node1.color with
                         | Gray ->
                             failwith
                               "Impossible: cycle detected after cycle detection has passed"
                         | Black -> (all_friends, all_files)
                         | White ->
                             ((let uu___2 = FStarC_Effect.op_Bang dbg in
                               if uu___2
                               then
                                 let uu___3 =
                                   FStarC_Class_Show.show
                                     (FStarC_Class_Show.show_list
                                        showable_dependence) dep_node1.edges in
                                 FStarC_Format.print2
                                   "Visiting %s: direct deps are %s\n"
                                   filename uu___3
                               else ());
                              deps_add_dep dep_graph1 filename
                                { edges = (dep_node1.edges); color = Gray };
                              (let uu___3 =
                                 let uu___4 =
                                   dependences_of file_system_map dep_graph1
                                     root_files filename in
                                 all_friend_deps dep_graph1 cycle
                                   (all_friends, all_files) uu___4 in
                               match uu___3 with
                               | (all_friends1, all_files1) ->
                                   (deps_add_dep dep_graph1 filename
                                      {
                                        edges = (dep_node1.edges);
                                        color = Black
                                      };
                                    (let uu___6 = FStarC_Effect.op_Bang dbg in
                                     if uu___6
                                     then
                                       FStarC_Format.print1 "Adding %s\n"
                                         filename
                                     else ());
                                    (let uu___6 =
                                       let uu___7 =
                                         FStarC_List.collect
                                           (fun uu___8 ->
                                              match uu___8 with
                                              | FriendImplementation m -> [m]
                                              | d -> []) dep_node1.edges in
                                       FStarC_List.op_At uu___7 all_friends1 in
                                     (uu___6, (filename :: all_files1)))))))
            and all_friend_deps dep_graph1 =
              fun cycle ->
                fun all_friends ->
                  fun filenames ->
                    FStarC_List.fold_left
                      (fun all_friends1 ->
                         fun k ->
                           all_friend_deps_1 dep_graph1 (k :: cycle)
                             all_friends1 k) all_friends filenames in
            let uu___ = all_friend_deps dep_graph [] ([], []) root_files in
            match uu___ with
            | (friends1, all_files_0) ->
                ((let uu___2 = FStarC_Effect.op_Bang dbg in
                  if uu___2
                  then
                    let uu___3 =
                      let uu___4 =
                        FStarC_Util.remove_dups (fun x -> fun y -> x = y)
                          friends1 in
                      FStarC_String.concat ", " uu___4 in
                    FStarC_Format.print3
                      "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
                      (FStarC_String.concat ", " all_files_0) uu___3
                      (FStarC_String.concat ", " interfaces_needing_inlining)
                  else ());
                 (let uu___2 =
                    widen_deps friends1 dep_graph file_system_map widened in
                  match uu___2 with
                  | (widened1, dep_graph1) ->
                      let uu___3 =
                        (let uu___5 = FStarC_Effect.op_Bang dbg in
                         if uu___5
                         then
                           FStarC_Format.print_string
                             "==============Phase2==================\n"
                         else ());
                        all_friend_deps dep_graph1 [] ([], []) root_files in
                      (match uu___3 with
                       | (uu___4, all_files) ->
                           ((let uu___6 = FStarC_Effect.op_Bang dbg in
                             if uu___6
                             then
                               FStarC_Format.print1
                                 "Phase2 complete: all_files = %s\n"
                                 (FStarC_String.concat ", " all_files)
                             else ());
                            (all_files, widened1)))))
let (phase1 :
  files_for_module_name ->
    dependence_graph ->
      module_name Prims.list -> Prims.bool -> (Prims.bool * dependence_graph))
  =
  fun file_system_map ->
    fun dep_graph ->
      fun interfaces_needing_inlining ->
        fun for_extraction ->
          (let uu___1 = FStarC_Effect.op_Bang dbg in
           if uu___1
           then
             FStarC_Format.print_string
               "==============Phase1==================\n"
           else ());
          (let widened = false in
           let uu___1 = (FStarC_Options.cmi ()) && for_extraction in
           if uu___1
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
  fun file_system_map ->
    fun dep_graph ->
      fun interfaces_needing_inlining ->
        fun root_files ->
          fun for_extraction ->
            let uu___ =
              phase1 file_system_map dep_graph interfaces_needing_inlining
                for_extraction in
            match uu___ with
            | (widened, dep_graph1) ->
                topological_dependences_of' file_system_map dep_graph1
                  interfaces_needing_inlining root_files widened
let (all_files_in_include_paths : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let paths = FStarC_Find.full_include_path () in
    FStarC_List.collect
      (fun path ->
         let files = safe_readdir_for_include path in
         let files1 =
           FStarC_List.filter
             (fun f ->
                (FStarC_Util.ends_with f ".fst") ||
                  (FStarC_Util.ends_with f ".fsti")) files in
         FStarC_List.map (fun file -> FStarC_Filepath.join_paths path file)
           files1) paths
let (collect :
  Prims.string Prims.list ->
    (Prims.string -> parsing_data FStar_Pervasives_Native.option) ->
      (Prims.string Prims.list * deps))
  =
  fun all_cmd_line_files ->
    fun get_parsing_data_from_cache ->
      FStarC_Stats.record "Parser.Dep.collect"
        (fun uu___ ->
           let all_cmd_line_files1 =
             match all_cmd_line_files with
             | [] -> all_files_in_include_paths ()
             | uu___1 -> all_cmd_line_files in
           let all_cmd_line_files2 =
             FStarC_List.map
               (fun fn ->
                  let uu___1 = FStarC_Find.find_file fn in
                  match uu___1 with
                  | FStar_Pervasives_Native.None ->
                      let uu___2 =
                        FStarC_Format.fmt1 "File %s could not be found" fn in
                      FStarC_Errors.raise_error0
                        FStarC_Errors_Codes.Fatal_ModuleOrFileNotFound ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic uu___2)
                  | FStar_Pervasives_Native.Some fn1 -> fn1)
               all_cmd_line_files1 in
           let dep_graph = deps_empty () in
           let file_system_map = build_map all_cmd_line_files2 in
           let interfaces_needing_inlining = FStarC_Effect.mk_ref [] in
           let add_interface_for_inlining l =
             let l1 = lowercase_module_name l in
             let uu___1 =
               let uu___2 = FStarC_Effect.op_Bang interfaces_needing_inlining in
               l1 :: uu___2 in
             FStarC_Effect.op_Colon_Equals interfaces_needing_inlining uu___1 in
           let parse_results = FStarC_SMap.create (Prims.of_int (40)) in
           let rec discover_one file_name1 =
             let uu___1 =
               let uu___2 = deps_try_find dep_graph file_name1 in
               uu___2 = FStar_Pervasives_Native.None in
             if uu___1
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Effect.op_Bang collect_one_cache in
                   FStarC_SMap.try_find uu___4 file_name1 in
                 match uu___3 with
                 | FStar_Pervasives_Native.Some cached ->
                     (empty_parsing_data, cached)
                 | FStar_Pervasives_Native.None ->
                     let uu___4 =
                       collect_one file_system_map file_name1
                         get_parsing_data_from_cache in
                     (match uu___4 with
                      | (parsing_data1, deps1, needs_interface_inlining,
                         additional_roots) ->
                          (parsing_data1,
                            (deps1, additional_roots,
                              needs_interface_inlining))) in
               match uu___2 with
               | (parsing_data1, (deps1, mo_roots, needs_interface_inlining))
                   ->
                   (if needs_interface_inlining
                    then add_interface_for_inlining file_name1
                    else ();
                    FStarC_SMap.add parse_results file_name1 parsing_data1;
                    (let deps2 =
                       let module_name1 = lowercase_module_name file_name1 in
                       let uu___5 =
                         (is_implementation file_name1) &&
                           (has_interface file_system_map module_name1) in
                       if uu___5
                       then
                         FStarC_List.op_At deps1 [UseInterface module_name1]
                       else deps1 in
                     let dep_node1 =
                       let uu___5 = FStarC_List.unique deps2 in
                       { edges = uu___5; color = White } in
                     deps_add_dep dep_graph file_name1 dep_node1;
                     (let uu___6 =
                        FStarC_List.map
                          (file_of_dep file_system_map all_cmd_line_files2)
                          (FStarC_List.op_At deps2 mo_roots) in
                      FStarC_List.iter discover_one uu___6)))
             else () in
           profile
             (fun uu___2 -> FStarC_List.iter discover_one all_cmd_line_files2)
             "FStarC.Parser.Dep.discover";
           (let cycle_detected dep_graph1 =
              fun cycle ->
                fun filename ->
                  let cycle1 = FStarC_List.rev cycle in
                  FStarC_Format.print1
                    "The cycle contains a subset of the modules in:\n  %s \n"
                    (FStarC_String.concat "\n  `uses` " cycle1);
                  (let fn = "dep.graph" in
                   with_file_outchannel fn
                     (fun outc ->
                        print_graph outc fn dep_graph1 file_system_map
                          all_cmd_line_files2);
                   FStarC_Format.print_string "\n";
                   (let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStarC_Format.fmt1
                            "Recursive dependency on module %s." filename in
                        FStarC_Errors_Msg.text uu___7 in
                      let uu___7 =
                        let uu___8 =
                          FStarC_Errors_Msg.text
                            "A full dependency graph was written to dep.graph." in
                        [uu___8] in
                      uu___6 :: uu___7 in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Fatal_CyclicDependence ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___5))) in
            let full_cycle_detection all_command_line_files =
              fun file_system_map1 ->
                let dep_graph1 = dep_graph_copy dep_graph in
                let mo_files = FStarC_Effect.mk_ref [] in
                let rec aux cycle =
                  fun filename ->
                    let node =
                      let uu___2 = deps_try_find dep_graph1 filename in
                      match uu___2 with
                      | FStar_Pervasives_Native.Some node1 -> node1
                      | FStar_Pervasives_Native.None ->
                          let uu___3 =
                            FStarC_Format.fmt1
                              "Impossible: Failed to find dependencies of %s"
                              filename in
                          failwith uu___3 in
                    let direct_deps =
                      FStarC_List.collect
                        (fun x ->
                           match x with
                           | UseInterface f ->
                               let uu___2 =
                                 implementation_of_internal file_system_map1
                                   f in
                               (match uu___2 with
                                | FStar_Pervasives_Native.None -> [x]
                                | FStar_Pervasives_Native.Some fn when
                                    fn = filename -> [x]
                                | uu___3 -> [x; UseImplementation f])
                           | PreferInterface f ->
                               let uu___2 =
                                 implementation_of_internal file_system_map1
                                   f in
                               (match uu___2 with
                                | FStar_Pervasives_Native.None -> [x]
                                | FStar_Pervasives_Native.Some fn when
                                    fn = filename -> [x]
                                | uu___3 -> [x; UseImplementation f])
                           | uu___2 -> [x]) node.edges in
                    match node.color with
                    | Gray -> cycle_detected dep_graph1 cycle filename
                    | Black -> ()
                    | White ->
                        (deps_add_dep dep_graph1 filename
                           { edges = direct_deps; color = Gray };
                         (let uu___4 =
                            dependences_of file_system_map1 dep_graph1
                              all_command_line_files filename in
                          FStarC_List.iter (fun k -> aux (k :: cycle) k)
                            uu___4);
                         deps_add_dep dep_graph1 filename
                           { edges = direct_deps; color = Black };
                         (let uu___5 = is_interface filename in
                          if uu___5
                          then
                            let uu___6 =
                              let uu___7 = lowercase_module_name filename in
                              implementation_of_internal file_system_map1
                                uu___7 in
                            FStarC_Option.iter
                              (fun impl ->
                                 if
                                   Prims.op_Negation
                                     (FStarC_List.contains impl
                                        all_command_line_files)
                                 then
                                   let uu___7 =
                                     let uu___8 =
                                       FStarC_Effect.op_Bang mo_files in
                                     impl :: uu___8 in
                                   FStarC_Effect.op_Colon_Equals mo_files
                                     uu___7
                                 else ()) uu___6
                          else ())) in
                FStarC_List.iter (aux []) all_command_line_files;
                (let uu___3 = FStarC_Effect.op_Bang mo_files in
                 FStarC_List.iter (aux []) uu___3) in
            full_cycle_detection all_cmd_line_files2 file_system_map;
            FStarC_List.iter
              (fun f ->
                 let m = lowercase_module_name f in
                 FStarC_Options.add_verify_module m) all_cmd_line_files2;
            (let inlining_ifaces =
               FStarC_Effect.op_Bang interfaces_needing_inlining in
             let uu___4 =
               profile
                 (fun uu___5 ->
                    let uu___6 =
                      let uu___7 = FStarC_Options.codegen () in
                      uu___7 <> FStar_Pervasives_Native.None in
                    topological_dependences_of file_system_map dep_graph
                      inlining_ifaces all_cmd_line_files2 uu___6)
                 "FStarC.Parser.Dep.topological_dependences_of" in
             match uu___4 with
             | (all_files, uu___5) ->
                 ((let uu___7 = FStarC_Effect.op_Bang dbg in
                   if uu___7
                   then
                     FStarC_Format.print1 "Interfaces needing inlining: %s\n"
                       (FStarC_String.concat ", " inlining_ifaces)
                   else ());
                  (all_files,
                    (mk_deps dep_graph file_system_map all_cmd_line_files2
                       all_files inlining_ifaces parse_results))))))
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun deps1 ->
    fun f ->
      dependences_of deps1.file_system_map deps1.dep_graph
        deps1.cmd_line_files f
let (deps_of_modul : deps -> module_name -> module_name Prims.list) =
  fun deps1 ->
    fun m ->
      let aux fopt =
        let uu___ =
          FStarC_Option.map
            (fun f ->
               let uu___1 = deps_of deps1 f in
               FStarC_List.map module_name_of_file uu___1) fopt in
        FStarC_Option.dflt [] uu___ in
      let uu___ =
        let uu___1 =
          FStarC_SMap.try_find deps1.file_system_map
            (FStarC_String.lowercase m) in
        FStarC_Option.map
          (fun uu___2 ->
             match uu___2 with
             | (intf_opt, impl_opt) ->
                 let uu___3 =
                   let uu___4 = aux intf_opt in
                   let uu___5 = aux impl_opt in
                   FStarC_List.op_At uu___4 uu___5 in
                 FStarC_Util.remove_dups (fun x -> fun y -> x = y) uu___3)
          uu___1 in
      FStarC_Option.dflt [] uu___
let (print_digest : (Prims.string * Prims.string) Prims.list -> Prims.string)
  =
  fun dig ->
    let uu___ =
      FStarC_List.map
        (fun uu___1 ->
           match uu___1 with
           | (m, d) ->
               let uu___2 = FStarC_Util.base64_encode d in
               FStarC_Format.fmt2 "%s:%s" m uu___2) dig in
    FStarC_String.concat "\n" uu___
let (print_make : FStarC_Util.out_channel -> deps -> unit) =
  fun outc ->
    fun deps1 ->
      let file_system_map = deps1.file_system_map in
      let all_cmd_line_files = deps1.cmd_line_files in
      let deps2 = deps1.dep_graph in
      let keys = deps_keys deps2 in
      FStarC_List.iter
        (fun f ->
           let dep_node1 =
             let uu___ = deps_try_find deps2 f in FStarC_Option.must uu___ in
           let files =
             FStarC_List.map (file_of_dep file_system_map all_cmd_line_files)
               dep_node1.edges in
           let files1 =
             FStarC_List.map (fun s -> FStarC_Util.replace_chars s 32 "\\ ")
               files in
           FStarC_Format.print2 "%s: %s\n\n" f
             (FStarC_String.concat " " files1)) keys
let (print_raw : FStarC_Util.out_channel -> deps -> unit) =
  fun outc ->
    fun deps1 ->
      let uu___ = deps1.dep_graph in
      match uu___ with
      | Deps deps2 ->
          let uu___1 =
            let uu___2 =
              FStarC_SMap.fold deps2
                (fun k ->
                   fun dep_node1 ->
                     fun out ->
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_List.map dep_to_string dep_node1.edges in
                           FStarC_String.concat ";\n\t" uu___5 in
                         FStarC_Format.fmt2 "%s -> [\n\t%s\n] " k uu___4 in
                       uu___3 :: out) [] in
            FStarC_String.concat ";;\n" uu___2 in
          FStarC_Util.fprint outc "%s\n" [uu___1]
let (print_full : FStarC_Util.out_channel -> deps -> unit) =
  fun outc ->
    fun deps1 ->
      let pre_tag = FStarC_Options_Ext.get "dep_pretag" in
      let sort_output_files orig_output_file_map =
        let order = FStarC_Effect.mk_ref [] in
        let remaining_output_files = FStarC_SMap.copy orig_output_file_map in
        let visited_other_modules = FStarC_SMap.create (Prims.of_int (41)) in
        let should_visit lc_module_name =
          (let uu___ =
             FStarC_SMap.try_find remaining_output_files lc_module_name in
           FStar_Pervasives_Native.uu___is_Some uu___) ||
            (let uu___ =
               FStarC_SMap.try_find visited_other_modules lc_module_name in
             FStar_Pervasives_Native.uu___is_None uu___) in
        let mark_visiting lc_module_name =
          let ml_file_opt =
            FStarC_SMap.try_find remaining_output_files lc_module_name in
          FStarC_SMap.remove remaining_output_files lc_module_name;
          FStarC_SMap.add visited_other_modules lc_module_name true;
          ml_file_opt in
        let emit_output_file_opt ml_file_opt =
          match ml_file_opt with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some ml_file ->
              let uu___ =
                let uu___1 = FStarC_Effect.op_Bang order in ml_file :: uu___1 in
              FStarC_Effect.op_Colon_Equals order uu___ in
        let rec aux uu___ =
          match uu___ with
          | [] -> ()
          | lc_module_name::modules_to_extract ->
              let visit_file file_opt =
                match file_opt with
                | FStar_Pervasives_Native.None -> ()
                | FStar_Pervasives_Native.Some file_name1 ->
                    let uu___1 = deps_try_find deps1.dep_graph file_name1 in
                    (match uu___1 with
                     | FStar_Pervasives_Native.None ->
                         let uu___2 =
                           FStarC_Format.fmt2
                             "Impossible: module %s: %s not found"
                             lc_module_name file_name1 in
                         failwith uu___2
                     | FStar_Pervasives_Native.Some
                         { edges = immediate_deps; color = uu___2;_} ->
                         let immediate_deps1 =
                           FStarC_List.map
                             (fun x ->
                                FStarC_String.lowercase
                                  (module_name_of_dep x)) immediate_deps in
                         aux immediate_deps1) in
              ((let uu___2 = should_visit lc_module_name in
                if uu___2
                then
                  let ml_file_opt = mark_visiting lc_module_name in
                  ((let uu___4 = implementation_of deps1 lc_module_name in
                    visit_file uu___4);
                   (let uu___5 = interface_of deps1 lc_module_name in
                    visit_file uu___5);
                   emit_output_file_opt ml_file_opt)
                else ());
               aux modules_to_extract) in
        let all_extracted_modules = FStarC_SMap.keys orig_output_file_map in
        aux all_extracted_modules;
        (let uu___1 = FStarC_Effect.op_Bang order in FStarC_List.rev uu___1) in
      let sb = FStarC_StringBuffer.create (Prims.of_int (10000)) in
      let pr str = let uu___ = FStarC_StringBuffer.add str sb in () in
      let norm_path s =
        FStarC_Util.replace_chars (FStarC_Util.replace_chars s 92 "/") 32
          "\\ " in
      let print_entry target =
        fun all_deps ->
          pr target;
          pr ":";
          FStarC_List.iter (fun f -> pr " \\\n\t"; pr (norm_path f)) all_deps;
          pr "\n\n" in
      let print_all tag =
        fun files ->
          pr (Prims.strcat pre_tag tag);
          pr "=";
          FStarC_List.iter (fun f -> pr " \\\n\t"; pr (norm_path f)) files;
          pr "\n\n" in
      let keys = deps_keys deps1.dep_graph in
      let no_fstar_stubs_file s =
        let s1 = "FStar.Stubs." in
        let s2 = "FStar." in
        let l1 = FStarC_String.length s1 in
        let uu___ =
          ((FStarC_String.length s) >= l1) &&
            (let uu___1 = FStarC_String.substring s Prims.int_zero l1 in
             uu___1 = s1) in
        if uu___
        then
          let uu___1 =
            FStarC_String.substring s l1 ((FStarC_String.length s) - l1) in
          Prims.strcat s2 uu___1
        else s in
      let output_file ext =
        fun fst_file ->
          let basename =
            let uu___ =
              let uu___1 = FStarC_Filepath.basename fst_file in
              check_and_strip_suffix uu___1 in
            FStarC_Option.must uu___ in
          let basename1 = no_fstar_stubs_file basename in
          let ml_base_name = FStarC_Util.replace_chars basename1 46 "_" in
          FStarC_Find.prepend_output_dir (Prims.strcat ml_base_name ext) in
      let output_fs_file f =
        let uu___ = output_file ".fs" f in norm_path uu___ in
      let output_ml_file f =
        let uu___ = output_file ".ml" f in norm_path uu___ in
      let output_krml_file f =
        let uu___ = output_file ".krml" f in norm_path uu___ in
      let output_cmx_file f =
        let uu___ = output_file ".cmx" f in norm_path uu___ in
      let cache_file f = let uu___ = cache_file_name f in norm_path uu___ in
      let uu___ =
        phase1 deps1.file_system_map deps1.dep_graph
          deps1.interfaces_with_inlining true in
      match uu___ with
      | (widened, dep_graph) ->
          let all_checked_files =
            FStarC_List.fold_left
              (fun all_checked_files1 ->
                 fun file_name1 ->
                   let process_one_key uu___1 =
                     let dep_node1 =
                       let uu___2 = deps_try_find deps1.dep_graph file_name1 in
                       FStarC_Option.must uu___2 in
                     let uu___2 =
                       let uu___3 = is_interface file_name1 in
                       if uu___3
                       then
                         (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.None)
                       else
                         (let uu___5 =
                            let uu___6 = lowercase_module_name file_name1 in
                            interface_of deps1 uu___6 in
                          match uu___5 with
                          | FStar_Pervasives_Native.None ->
                              (FStar_Pervasives_Native.None,
                                FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some iface ->
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      deps_try_find deps1.dep_graph iface in
                                    FStarC_Option.must uu___9 in
                                  uu___8.edges in
                                FStar_Pervasives_Native.Some uu___7 in
                              ((FStar_Pervasives_Native.Some iface), uu___6)) in
                     match uu___2 with
                     | (iface_fn, iface_deps) ->
                         let iface_deps1 =
                           FStarC_Option.map
                             (FStarC_List.filter
                                (fun iface_dep ->
                                   let uu___3 =
                                     FStarC_Util.for_some
                                       (dep_subsumed_by iface_dep)
                                       dep_node1.edges in
                                   Prims.op_Negation uu___3)) iface_deps in
                         let files =
                           FStarC_List.map
                             (file_of_dep_aux true deps1.file_system_map
                                deps1.cmd_line_files) dep_node1.edges in
                         let files1 =
                           match iface_deps1 with
                           | FStar_Pervasives_Native.None -> files
                           | FStar_Pervasives_Native.Some iface_deps2 ->
                               let iface_files =
                                 FStarC_List.map
                                   (file_of_dep_aux true
                                      deps1.file_system_map
                                      deps1.cmd_line_files) iface_deps2 in
                               FStarC_Util.remove_dups
                                 (fun x -> fun y -> x = y)
                                 (FStarC_List.op_At files iface_files) in
                         let files2 =
                           if FStar_Pervasives_Native.uu___is_Some iface_fn
                           then
                             let iface_fn1 = FStarC_Option.must iface_fn in
                             let uu___3 =
                               FStarC_List.filter (fun f -> f <> iface_fn1)
                                 files1 in
                             let uu___4 = cache_file_name iface_fn1 in uu___4
                               :: uu___3
                           else files1 in
                         let cache_file_name1 = cache_file file_name1 in
                         let all_checked_files2 =
                           let uu___3 =
                             let uu___4 =
                               let uu___5 = module_name_of_file file_name1 in
                               FStarC_Options.should_be_already_cached uu___5 in
                             Prims.op_Negation uu___4 in
                           if uu___3
                           then
                             (print_entry cache_file_name1 (file_name1 ::
                                files2);
                              cache_file_name1
                              ::
                              all_checked_files1)
                           else all_checked_files1 in
                         let uu___3 =
                           let uu___4 = FStarC_Options.cmi () in
                           if uu___4
                           then
                             profile
                               (fun uu___5 ->
                                  let uu___6 = dep_graph_copy dep_graph in
                                  topological_dependences_of'
                                    deps1.file_system_map uu___6
                                    deps1.interfaces_with_inlining
                                    [file_name1] widened)
                               "FStarC.Parser.Dep.topological_dependences_of_2"
                           else
                             (let maybe_widen_deps f_deps =
                                FStarC_List.map
                                  (fun dep ->
                                     file_of_dep_aux false
                                       deps1.file_system_map
                                       deps1.cmd_line_files dep) f_deps in
                              let fst_files =
                                maybe_widen_deps dep_node1.edges in
                              let fst_files_from_iface =
                                match iface_deps1 with
                                | FStar_Pervasives_Native.None -> []
                                | FStar_Pervasives_Native.Some iface_deps2 ->
                                    maybe_widen_deps iface_deps2 in
                              let uu___6 =
                                FStarC_Util.remove_dups
                                  (fun x -> fun y -> x = y)
                                  (FStarC_List.op_At fst_files
                                     fst_files_from_iface) in
                              (uu___6, false)) in
                         (match uu___3 with
                          | (all_fst_files_dep, widened1) ->
                              let all_checked_fst_dep_files =
                                FStarC_List.map cache_file all_fst_files_dep in
                              ((let uu___5 = is_implementation file_name1 in
                                if uu___5
                                then
                                  ((let uu___7 =
                                      (FStarC_Options.cmi ()) && widened1 in
                                    if uu___7
                                    then
                                      let mname =
                                        lowercase_module_name file_name1 in
                                      ((let uu___9 =
                                          output_ml_file file_name1 in
                                        print_entry uu___9 (cache_file_name1
                                          :: all_checked_fst_dep_files));
                                       (let uu___10 =
                                          FStarC_Options.should_extract mname
                                            FStarC_Options.FSharp in
                                        if uu___10
                                        then
                                          let uu___11 =
                                            output_fs_file file_name1 in
                                          print_entry uu___11
                                            (cache_file_name1 ::
                                            all_checked_fst_dep_files)
                                        else ());
                                       (let uu___10 =
                                          output_krml_file file_name1 in
                                        print_entry uu___10 (cache_file_name1
                                          :: all_checked_fst_dep_files)))
                                    else
                                      (let mname =
                                         lowercase_module_name file_name1 in
                                       (let uu___10 =
                                          output_ml_file file_name1 in
                                        print_entry uu___10
                                          [cache_file_name1]);
                                       (let uu___11 =
                                          FStarC_Options.should_extract mname
                                            FStarC_Options.FSharp in
                                        if uu___11
                                        then
                                          let uu___12 =
                                            output_fs_file file_name1 in
                                          print_entry uu___12
                                            [cache_file_name1]
                                        else ());
                                       (let uu___11 =
                                          output_krml_file file_name1 in
                                        print_entry uu___11
                                          [cache_file_name1])));
                                   (let cmx_files =
                                      let extracted_fst_files =
                                        FStarC_List.filter
                                          (fun df ->
                                             (let uu___7 =
                                                lowercase_module_name df in
                                              let uu___8 =
                                                lowercase_module_name
                                                  file_name1 in
                                              uu___7 <> uu___8) &&
                                               (let uu___7 =
                                                  lowercase_module_name df in
                                                FStarC_Options.should_extract
                                                  uu___7 FStarC_Options.OCaml))
                                          all_fst_files_dep in
                                      FStarC_List.map output_cmx_file
                                        extracted_fst_files in
                                    let uu___7 =
                                      let uu___8 =
                                        lowercase_module_name file_name1 in
                                      FStarC_Options.should_extract uu___8
                                        FStarC_Options.OCaml in
                                    if uu___7
                                    then
                                      let uu___8 = output_cmx_file file_name1 in
                                      let uu___9 =
                                        let uu___10 =
                                          output_ml_file file_name1 in
                                        uu___10 :: cmx_files in
                                      print_entry uu___8 uu___9
                                    else ()))
                                else
                                  (let uu___7 =
                                     (let uu___8 =
                                        let uu___9 =
                                          lowercase_module_name file_name1 in
                                        has_implementation
                                          deps1.file_system_map uu___9 in
                                      Prims.op_Negation uu___8) &&
                                       (is_interface file_name1) in
                                   if uu___7
                                   then
                                     let uu___8 =
                                       (FStarC_Options.cmi ()) &&
                                         (widened1 || true) in
                                     (if uu___8
                                      then
                                        let uu___9 =
                                          output_krml_file file_name1 in
                                        print_entry uu___9 (cache_file_name1
                                          :: all_checked_fst_dep_files)
                                      else
                                        (let uu___10 =
                                           output_krml_file file_name1 in
                                         print_entry uu___10
                                           [cache_file_name1]))
                                   else ()));
                               all_checked_files2)) in
                   profile process_one_key
                     "FStarC.Parser.Dep.process_one_key") [] keys in
          let all_fst_files =
            let uu___1 = FStarC_List.filter is_implementation keys in
            FStarC_Util.sort_with FStarC_String.compare uu___1 in
          let all_fsti_files =
            let uu___1 = FStarC_List.filter is_interface keys in
            FStarC_Util.sort_with FStarC_String.compare uu___1 in
          let all_ml_files =
            let ml_file_map = FStarC_SMap.create (Prims.of_int (41)) in
            FStarC_List.iter
              (fun fst_file ->
                 let mname = lowercase_module_name fst_file in
                 let uu___2 =
                   FStarC_Options.should_extract mname FStarC_Options.OCaml in
                 if uu___2
                 then
                   let uu___3 = output_ml_file fst_file in
                   FStarC_SMap.add ml_file_map mname uu___3
                 else ()) all_fst_files;
            sort_output_files ml_file_map in
          let all_fs_files =
            let fs_file_map = FStarC_SMap.create (Prims.of_int (41)) in
            FStarC_List.iter
              (fun fst_file ->
                 let mname = lowercase_module_name fst_file in
                 let uu___2 =
                   FStarC_Options.should_extract mname FStarC_Options.FSharp in
                 if uu___2
                 then
                   let uu___3 = output_fs_file fst_file in
                   FStarC_SMap.add fs_file_map mname uu___3
                 else ()) all_fst_files;
            sort_output_files fs_file_map in
          let all_krml_files =
            let krml_file_map = FStarC_SMap.create (Prims.of_int (41)) in
            FStarC_List.iter
              (fun fst_file ->
                 let mname = lowercase_module_name fst_file in
                 let uu___2 =
                   FStarC_Options.should_extract mname FStarC_Options.Krml in
                 if uu___2
                 then
                   let uu___3 = output_krml_file fst_file in
                   FStarC_SMap.add krml_file_map mname uu___3
                 else ()) keys;
            sort_output_files krml_file_map in
          (FStarC_List.iter
             (fun fsti ->
                let mn = lowercase_module_name fsti in
                let range_of_file fsti1 =
                  let r =
                    FStarC_Range_Ops.set_file_of_range
                      FStarC_Range_Type.dummyRange fsti1 in
                  let uu___2 = FStarC_Range_Type.def_range r in
                  FStarC_Range_Type.set_use_range r uu___2 in
                let uu___2 =
                  let uu___3 = has_implementation deps1.file_system_map mn in
                  Prims.op_Negation uu___3 in
                if uu___2
                then
                  let uu___3 = range_of_file fsti in
                  let uu___4 =
                    let uu___5 = module_name_of_file fsti in
                    FStarC_Format.fmt1
                      "Interface %s is admitted without an implementation"
                      uu___5 in
                  FStarC_Errors.log_issue
                    FStarC_Class_HasRange.hasRange_range uu___3
                    FStarC_Errors_Codes.Warning_WarnOnUse ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___4)
                else ()) all_fsti_files;
           print_all "ALL_FST_FILES" all_fst_files;
           print_all "ALL_FSTI_FILES" all_fsti_files;
           print_all "ALL_CHECKED_FILES" all_checked_files;
           print_all "ALL_FS_FILES" all_fs_files;
           print_all "ALL_ML_FILES" all_ml_files;
           print_all "ALL_KRML_FILES" all_krml_files;
           FStarC_StringBuffer.output_channel outc sb)
let (do_print : FStarC_Util.out_channel -> Prims.string -> deps -> unit) =
  fun outc ->
    fun fn ->
      fun deps1 ->
        let pref uu___ =
          (let uu___2 =
             let uu___3 = FStarC_Effect.op_Bang FStarC_Options._version in
             [uu___3] in
           FStarC_Util.fprint outc "# This .depend was generated by F* %s\n"
             uu___2);
          (let uu___3 =
             let uu___4 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_string
                 FStarC_Util.exec_name in
             [uu___4] in
           FStarC_Util.fprint outc "# Executable: %s\n" uu___3);
          (let uu___4 =
             let uu___5 = FStarC_Effect.op_Bang FStarC_Options._commit in
             [uu___5] in
           FStarC_Util.fprint outc "# Hash: %s\n" uu___4);
          (let uu___5 =
             let uu___6 =
               let uu___7 =
                 let uu___8 = FStarC_Util.getcwd () in
                 FStarC_Filepath.normalize_file_path uu___8 in
               FStarC_Class_Show.show FStarC_Class_Show.showable_string
                 uu___7 in
             [uu___6] in
           FStarC_Util.fprint outc "# Running in directory %s\n" uu___5);
          (let uu___6 =
             let uu___7 =
               let uu___8 = FStarC_Util.get_cmd_args () in
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string) uu___8 in
             [uu___7] in
           FStarC_Util.fprint outc "# Command line arguments: \"%s\"\n"
             uu___6);
          FStarC_Util.fprint outc "\n" [] in
        let uu___ = FStarC_Options.dep () in
        match uu___ with
        | FStar_Pervasives_Native.Some "make" ->
            (pref (); print_make outc deps1)
        | FStar_Pervasives_Native.Some "full" ->
            (pref ();
             profile (fun uu___2 -> print_full outc deps1)
               "FStarC.Parser.Deps.print_full_deps")
        | FStar_Pervasives_Native.Some "graph" ->
            print_graph outc fn deps1.dep_graph deps1.file_system_map
              deps1.cmd_line_files
        | FStar_Pervasives_Native.Some "raw" -> print_raw outc deps1
        | FStar_Pervasives_Native.Some uu___1 ->
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_UnknownToolForDep ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic "unknown tool for --dep\n")
        | FStar_Pervasives_Native.None -> ()
let (do_print_stdout : deps -> unit) =
  fun deps1 -> do_print FStarC_Util.stdout "<stdout>" deps1
let (do_print_file : deps -> Prims.string -> unit) =
  fun deps1 ->
    fun fn -> with_file_outchannel fn (fun outc -> do_print outc fn deps1)
let (print : deps -> unit) =
  fun deps1 ->
    let uu___ = FStarC_Options.output_deps_to () in
    match uu___ with
    | FStar_Pervasives_Native.Some s -> do_print_file deps1 s
    | FStar_Pervasives_Native.None when
        let uu___1 = FStarC_Options.dep () in
        uu___1 = (FStar_Pervasives_Native.Some "graph") ->
        do_print_file deps1 "dep.graph"
    | FStar_Pervasives_Native.None -> do_print_stdout deps1
let (module_has_interface : deps -> FStarC_Ident.lident -> Prims.bool) =
  fun deps1 ->
    fun module_name1 ->
      let uu___ =
        let uu___1 = FStarC_Ident.string_of_lid module_name1 in
        FStarC_String.lowercase uu___1 in
      has_interface deps1.file_system_map uu___
let (deps_has_implementation : deps -> FStarC_Ident.lident -> Prims.bool) =
  fun deps1 ->
    fun module_name1 ->
      let m =
        let uu___ = FStarC_Ident.string_of_lid module_name1 in
        FStarC_String.lowercase uu___ in
      FStarC_Util.for_some
        (fun f ->
           (is_implementation f) &&
             (let uu___ =
                let uu___1 = module_name_of_file f in
                FStarC_String.lowercase uu___1 in
              uu___ = m)) deps1.all_files
