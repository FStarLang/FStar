open Prims
let fd_enabled : Prims.bool FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let fly_deps_enabled (uu___ : unit) : Prims.bool=
  let uu___1 = FStarC_Effect.op_Bang fd_enabled in
  match uu___1 with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None ->
      let res =
        let uu___2 = FStarC_Options_Ext.enabled "fly_deps" in
        if uu___2
        then
          let uu___3 =
            (let uu___4 = FStarC_Options.dep () in
             FStar_Pervasives_Native.uu___is_Some uu___4) ||
              (FStarC_Options.any_dump_module ()) in
          (if uu___3
           then
             ((let uu___5 = FStarC_Debug.any () in
               if uu___5
               then
                 FStarC_Format.print_string
                   "Ignoring fly_deps because dep or dump_module is on\n"
               else ());
              false)
           else
             ((let uu___6 = FStarC_Debug.any () in
               if uu___6
               then FStarC_Format.print_string "fly_deps is on!\n"
               else ());
              true))
        else
          ((let uu___5 = FStarC_Debug.any () in
            if uu___5
            then FStarC_Format.print_string "fly_deps is off!\n"
            else ());
           false) in
      (FStarC_Format.flush_stdout ();
       FStarC_Effect.op_Colon_Equals fd_enabled
         (FStar_Pervasives_Native.Some res);
       res)
let with_fly_deps_disabled (f : unit -> 'a) : 'a=
  let v = FStarC_Effect.op_Bang fd_enabled in
  FStarC_Effect.op_Colon_Equals fd_enabled
    (FStar_Pervasives_Native.Some false);
  FStarC_Util.finally
    (fun uu___1 -> FStarC_Effect.op_Colon_Equals fd_enabled v) f
let debug_fly_deps : unit -> Prims.bool=
  let dbg = FStarC_Debug.get_toggle "fly_deps" in
  fun uu___ -> FStarC_Effect.op_Bang dbg
type open_kind =
  | Open_module 
  | Open_namespace 
let uu___is_Open_module (projectee : open_kind) : Prims.bool=
  match projectee with | Open_module -> true | uu___ -> false
let uu___is_Open_namespace (projectee : open_kind) : Prims.bool=
  match projectee with | Open_namespace -> true | uu___ -> false
type parsing_data_elt =
  | P_begin_module of FStarC_Ident.lident 
  | P_open of (Prims.bool * FStarC_Ident.lident) 
  | P_implicit_open_module_or_namespace of (open_kind * FStarC_Ident.lid) 
  | P_dep of (Prims.bool * FStarC_Ident.lident) 
  | P_alias of (FStarC_Ident.ident * FStarC_Ident.lident) 
  | P_lid of FStarC_Ident.lident 
  | P_inline_for_extraction 
let uu___is_P_begin_module (projectee : parsing_data_elt) : Prims.bool=
  match projectee with | P_begin_module _0 -> true | uu___ -> false
let __proj__P_begin_module__item___0 (projectee : parsing_data_elt) :
  FStarC_Ident.lident= match projectee with | P_begin_module _0 -> _0
let uu___is_P_open (projectee : parsing_data_elt) : Prims.bool=
  match projectee with | P_open _0 -> true | uu___ -> false
let __proj__P_open__item___0 (projectee : parsing_data_elt) :
  (Prims.bool * FStarC_Ident.lident)= match projectee with | P_open _0 -> _0
let uu___is_P_implicit_open_module_or_namespace
  (projectee : parsing_data_elt) : Prims.bool=
  match projectee with
  | P_implicit_open_module_or_namespace _0 -> true
  | uu___ -> false
let __proj__P_implicit_open_module_or_namespace__item___0
  (projectee : parsing_data_elt) : (open_kind * FStarC_Ident.lid)=
  match projectee with | P_implicit_open_module_or_namespace _0 -> _0
let uu___is_P_dep (projectee : parsing_data_elt) : Prims.bool=
  match projectee with | P_dep _0 -> true | uu___ -> false
let __proj__P_dep__item___0 (projectee : parsing_data_elt) :
  (Prims.bool * FStarC_Ident.lident)= match projectee with | P_dep _0 -> _0
let uu___is_P_alias (projectee : parsing_data_elt) : Prims.bool=
  match projectee with | P_alias _0 -> true | uu___ -> false
let __proj__P_alias__item___0 (projectee : parsing_data_elt) :
  (FStarC_Ident.ident * FStarC_Ident.lident)=
  match projectee with | P_alias _0 -> _0
let uu___is_P_lid (projectee : parsing_data_elt) : Prims.bool=
  match projectee with | P_lid _0 -> true | uu___ -> false
let __proj__P_lid__item___0 (projectee : parsing_data_elt) :
  FStarC_Ident.lident= match projectee with | P_lid _0 -> _0
let uu___is_P_inline_for_extraction (projectee : parsing_data_elt) :
  Prims.bool=
  match projectee with | P_inline_for_extraction -> true | uu___ -> false
type module_name = Prims.string
let remove_dups_fast (uu___ : 'a FStarC_Class_Ord.ord) (xs : 'a Prims.list) :
  'a Prims.list=
  let uu___1 =
    let uu___2 =
      let uu___3 =
        Obj.magic
          (FStarC_Class_Setlike.empty ()
             (Obj.magic (FStarC_RBSet.setlike_rbset uu___)) ()) in
      ([], uu___3) in
    FStarC_List.fold_left
      (fun uu___3 x ->
         match uu___3 with
         | (acc, acc_set) ->
             let uu___4 =
               FStarC_Class_Setlike.mem ()
                 (Obj.magic (FStarC_RBSet.setlike_rbset uu___)) x
                 (Obj.magic acc_set) in
             if uu___4
             then (acc, acc_set)
             else
               (let uu___6 =
                  Obj.magic
                    (FStarC_Class_Setlike.add ()
                       (Obj.magic (FStarC_RBSet.setlike_rbset uu___)) x
                       (Obj.magic acc_set)) in
                ((x :: acc), uu___6))) uu___2 xs in
  match uu___1 with | (acc, uu___2) -> FStarC_List.rev acc
let dbg : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Dep"
let dbg_CheckedFiles : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "CheckedFiles"
let debug_print (f : unit -> unit) : unit=
  let uu___ = FStarC_Effect.op_Bang dbg in if uu___ then f () else ()
let profile (f : unit -> 'uuuuu) (c : Prims.string) : 'uuuuu=
  FStarC_Profiling.profile f FStar_Pervasives_Native.None c
let with_file_outchannel (fn : Prims.string)
  (k : FStarC_Util.out_channel -> 'a) : 'a=
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
let uu___is_VerifyAll (projectee : verify_mode) : Prims.bool=
  match projectee with | VerifyAll -> true | uu___ -> false
let uu___is_VerifyUserList (projectee : verify_mode) : Prims.bool=
  match projectee with | VerifyUserList -> true | uu___ -> false
let uu___is_VerifyFigureItOut (projectee : verify_mode) : Prims.bool=
  match projectee with | VerifyFigureItOut -> true | uu___ -> false
type intf_and_impl =
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)
type files_for_module_name = intf_and_impl FStarC_SMap.t
let intf_and_impl_to_string
  (ii :
    (Prims.string FStar_Pervasives_Native.option * Prims.string
      FStar_Pervasives_Native.option))
  : Prims.string=
  match ii with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      "<None>, <None>"
  | (FStar_Pervasives_Native.Some intf, FStar_Pervasives_Native.None) -> intf
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some impl) -> impl
  | (FStar_Pervasives_Native.Some intf, FStar_Pervasives_Native.Some impl) ->
      Prims.strcat intf (Prims.strcat ", " impl)
let files_for_module_name_to_string (m : files_for_module_name) : unit=
  FStarC_Format.print_string "Printing the file system map {\n";
  (let str_opt_to_string sopt =
     match sopt with
     | FStar_Pervasives_Native.None -> "<None>"
     | FStar_Pervasives_Native.Some s -> s in
   FStarC_SMap.iter m
     (fun k v -> FStarC_Format.print2 "%s:%s\n" k (intf_and_impl_to_string v));
   FStarC_Format.print_string "}\n")
type color =
  | White 
  | Gray 
  | Black 
let uu___is_White (projectee : color) : Prims.bool=
  match projectee with | White -> true | uu___ -> false
let uu___is_Gray (projectee : color) : Prims.bool=
  match projectee with | Gray -> true | uu___ -> false
let uu___is_Black (projectee : color) : Prims.bool=
  match projectee with | Black -> true | uu___ -> false
let all_file_suffixes (uu___ : unit) : Prims.string Prims.list=
  let lang_exts =
    let uu___1 = FStarC_Options.lang_extensions () in
    FStarC_List.map (fun ext -> Prims.strcat "." ext) uu___1 in
  let base = ".fst" :: lang_exts in
  let uu___1 = FStarC_List.map (fun ext -> Prims.strcat ext "i") base in
  FStarC_List.op_At base uu___1
let check_and_strip_suffix (f : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let matches =
    let uu___ = all_file_suffixes () in
    FStarC_List.map
      (fun ext ->
         let lext = FStarC_String.length ext in
         let l = FStarC_String.length f in
         let uu___1 =
           (l > lext) &&
             (let uu___2 = FStarC_String.substring f (l - lext) lext in
              uu___2 = ext) in
         if uu___1
         then
           let uu___2 = FStarC_String.substring f Prims.int_zero (l - lext) in
           FStar_Pervasives_Native.Some uu___2
         else FStar_Pervasives_Native.None) uu___ in
  let uu___ = FStarC_List.filter FStar_Pervasives_Native.uu___is_Some matches in
  match uu___ with
  | (FStar_Pervasives_Native.Some m)::uu___1 ->
      FStar_Pervasives_Native.Some m
  | uu___1 -> FStar_Pervasives_Native.None
let is_interface (f : Prims.string) : Prims.bool=
  let uu___ = FStarC_String.get f ((FStarC_String.length f) - Prims.int_one) in
  uu___ = 105
let implementation_of_file (f : Prims.string) : Prims.string=
  let uu___ = is_interface f in
  if uu___
  then
    FStarC_String.substring f Prims.int_zero
      ((FStarC_String.length f) - Prims.int_one)
  else f
let is_implementation (f : Prims.string) : Prims.bool=
  let uu___ = is_interface f in Prims.op_Negation uu___
type parsing_data =
  {
  elts: parsing_data_elt Prims.list ;
  no_prelude: Prims.bool }
let __proj__Mkparsing_data__item__elts (projectee : parsing_data) :
  parsing_data_elt Prims.list=
  match projectee with | { elts; no_prelude;_} -> elts
let __proj__Mkparsing_data__item__no_prelude (projectee : parsing_data) :
  Prims.bool= match projectee with | { elts; no_prelude;_} -> no_prelude
let list_of_option (uu___ : 'uuuuu FStar_Pervasives_Native.option) :
  'uuuuu Prims.list=
  match uu___ with
  | FStar_Pervasives_Native.Some x -> [x]
  | FStar_Pervasives_Native.None -> []
let list_of_pair
  (uu___ :
    ('uuuuu FStar_Pervasives_Native.option * 'uuuuu
      FStar_Pervasives_Native.option))
  : 'uuuuu Prims.list=
  match uu___ with
  | (intf, impl) ->
      FStarC_List.op_At (list_of_option intf) (list_of_option impl)
let maybe_module_name_of_file (f : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = FStarC_Filepath.basename f in check_and_strip_suffix uu___
let module_name_of_file (f : Prims.string) : Prims.string=
  let uu___ = maybe_module_name_of_file f in
  match uu___ with
  | FStar_Pervasives_Native.Some longname -> longname
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Format.fmt1 "Not a valid FStar file: '%s'" f in
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
      FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_NotValidFStarFile
        () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___1)
let lowercase_module_name (f : Prims.string) : Prims.string=
  let uu___ = module_name_of_file f in FStarC_String.lowercase uu___
let namespace_of_module (f : Prims.string) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
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
let uu___is_UseInterface (projectee : dependence) : Prims.bool=
  match projectee with | UseInterface _0 -> true | uu___ -> false
let __proj__UseInterface__item___0 (projectee : dependence) : module_name=
  match projectee with | UseInterface _0 -> _0
let uu___is_PreferInterface (projectee : dependence) : Prims.bool=
  match projectee with | PreferInterface _0 -> true | uu___ -> false
let __proj__PreferInterface__item___0 (projectee : dependence) : module_name=
  match projectee with | PreferInterface _0 -> _0
let uu___is_UseImplementation (projectee : dependence) : Prims.bool=
  match projectee with | UseImplementation _0 -> true | uu___ -> false
let __proj__UseImplementation__item___0 (projectee : dependence) :
  module_name= match projectee with | UseImplementation _0 -> _0
let uu___is_FriendImplementation (projectee : dependence) : Prims.bool=
  match projectee with | FriendImplementation _0 -> true | uu___ -> false
let __proj__FriendImplementation__item___0 (projectee : dependence) :
  module_name= match projectee with | FriendImplementation _0 -> _0
let dep_to_string (uu___ : dependence) : Prims.string=
  match uu___ with
  | UseInterface f -> Prims.strcat "UseInterface " f
  | PreferInterface f -> Prims.strcat "PreferInterface " f
  | UseImplementation f -> Prims.strcat "UseImplementation " f
  | FriendImplementation f -> Prims.strcat "FriendImplementation " f
let showable_dependence : dependence FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = dep_to_string }
type dependences = dependence Prims.list
let empty_dependences (uu___ : unit) : 'uuuuu Prims.list= []
type dep_node = {
  edges: dependences ;
  color: color }
let __proj__Mkdep_node__item__edges (projectee : dep_node) : dependences=
  match projectee with | { edges; color = color1;_} -> edges
let __proj__Mkdep_node__item__color (projectee : dep_node) : color=
  match projectee with | { edges; color = color1;_} -> color1
type dependence_graph =
  | Deps of dep_node FStarC_SMap.t 
let uu___is_Deps (projectee : dependence_graph) : Prims.bool= true
let __proj__Deps__item___0 (projectee : dependence_graph) :
  dep_node FStarC_SMap.t= match projectee with | Deps _0 -> _0
let copy_dep_graph (d : dependence_graph) : dependence_graph=
  let uu___ = d in
  match uu___ with | Deps m -> let uu___1 = FStarC_SMap.copy m in Deps uu___1
let str_of_parsing_data_elt (elt : parsing_data_elt) : Prims.string=
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
        let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
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
let showable_parsing_data_elt : parsing_data_elt FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = str_of_parsing_data_elt }
let str_of_parsing_data (pd : parsing_data) : Prims.string=
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
let showable_parsing_data : parsing_data FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = str_of_parsing_data }
let friends (p : parsing_data) : FStarC_Ident.lident Prims.list=
  FStarC_List.collect
    (fun uu___ -> match uu___ with | P_dep (true, l) -> [l] | uu___1 -> [])
    p.elts
let parsing_data_elt_eq (e1 : parsing_data_elt) (e2 : parsing_data_elt) :
  Prims.bool=
  match (e1, e2) with
  | (P_begin_module l1, P_begin_module l2) -> FStarC_Ident.lid_equals l1 l2
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
let empty_parsing_data : parsing_data= { elts = []; no_prelude = false }
type deps =
  {
  dep_graph: dependence_graph ;
  file_system_map: files_for_module_name ;
  valid_namespaces: Prims.string Prims.list FStarC_SMap.t ;
  cmd_line_files: file_name Prims.list ;
  all_files: file_name FStarC_RBSet.t FStarC_Effect.ref ;
  interfaces_with_inlining: module_name Prims.list ;
  parse_results: parsing_data FStarC_SMap.t }
let __proj__Mkdeps__item__dep_graph (projectee : deps) : dependence_graph=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} -> dep_graph
let __proj__Mkdeps__item__file_system_map (projectee : deps) :
  files_for_module_name=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} ->
      file_system_map
let __proj__Mkdeps__item__valid_namespaces (projectee : deps) :
  Prims.string Prims.list FStarC_SMap.t=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} ->
      valid_namespaces
let __proj__Mkdeps__item__cmd_line_files (projectee : deps) :
  file_name Prims.list=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} -> cmd_line_files
let __proj__Mkdeps__item__all_files (projectee : deps) :
  file_name FStarC_RBSet.t FStarC_Effect.ref=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} -> all_files
let __proj__Mkdeps__item__interfaces_with_inlining (projectee : deps) :
  module_name Prims.list=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} ->
      interfaces_with_inlining
let __proj__Mkdeps__item__parse_results (projectee : deps) :
  parsing_data FStarC_SMap.t=
  match projectee with
  | { dep_graph; file_system_map; valid_namespaces; cmd_line_files;
      all_files; interfaces_with_inlining; parse_results;_} -> parse_results
let copy_deps (d : deps) : deps=
  let uu___ = copy_dep_graph d.dep_graph in
  let uu___1 =
    let uu___2 = FStarC_Effect.op_Bang d.all_files in
    FStarC_Effect.mk_ref uu___2 in
  {
    dep_graph = uu___;
    file_system_map = (d.file_system_map);
    valid_namespaces = (d.valid_namespaces);
    cmd_line_files = (d.cmd_line_files);
    all_files = uu___1;
    interfaces_with_inlining = (d.interfaces_with_inlining);
    parse_results = (d.parse_results)
  }
let deps_try_find (uu___ : dependence_graph) (k : Prims.string) :
  dep_node FStar_Pervasives_Native.option=
  match uu___ with | Deps m -> FStarC_SMap.try_find m k
let deps_add_dep (uu___ : dependence_graph) (k : Prims.string) (v : dep_node)
  : unit= match uu___ with | Deps m -> FStarC_SMap.add m k v
let deps_keys (uu___ : dependence_graph) : Prims.string Prims.list=
  match uu___ with | Deps m -> FStarC_SMap.keys m
let deps_empty (uu___ : unit) : dependence_graph=
  let uu___1 = FStarC_SMap.create (Prims.of_int (41)) in Deps uu___1
let mk_deps (dg : dependence_graph) (fs : files_for_module_name)
  (ns : Prims.string Prims.list FStarC_SMap.t) (c : file_name Prims.list)
  (a : file_name FStarC_RBSet.t) (i : module_name Prims.list)
  (pr : parsing_data FStarC_SMap.t) : deps=
  let uu___ = FStarC_Effect.mk_ref a in
  {
    dep_graph = dg;
    file_system_map = fs;
    valid_namespaces = ns;
    cmd_line_files = c;
    all_files = uu___;
    interfaces_with_inlining = i;
    parse_results = pr
  }
let empty_deps (clf : Prims.string Prims.list) : deps=
  let uu___ = deps_empty () in
  let uu___1 = FStarC_SMap.create Prims.int_zero in
  let uu___2 = FStarC_SMap.create Prims.int_zero in
  let uu___3 =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
         ()) in
  let uu___4 = FStarC_SMap.create Prims.int_zero in
  mk_deps uu___ uu___1 uu___2 clf uu___3 [] uu___4
let module_name_of_dep (uu___ : dependence) : module_name=
  match uu___ with
  | UseInterface m -> m
  | PreferInterface m -> m
  | UseImplementation m -> m
  | FriendImplementation m -> m
let resolve_module_name (file_system_map : files_for_module_name)
  (key : module_name) : module_name FStar_Pervasives_Native.option=
  let uu___ = FStarC_SMap.try_find file_system_map key in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some fn, uu___1) ->
      let uu___2 = lowercase_module_name fn in
      FStar_Pervasives_Native.Some uu___2
  | FStar_Pervasives_Native.Some (uu___1, FStar_Pervasives_Native.Some fn) ->
      let uu___2 = lowercase_module_name fn in
      FStar_Pervasives_Native.Some uu___2
  | uu___1 -> FStar_Pervasives_Native.None
let interface_of_internal (file_system_map : files_for_module_name)
  (key : module_name) : file_name FStar_Pervasives_Native.option=
  let uu___ = FStarC_SMap.try_find file_system_map key in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some iface, uu___1)
      -> FStar_Pervasives_Native.Some iface
  | uu___1 -> FStar_Pervasives_Native.None
let implementation_of_internal (file_system_map : files_for_module_name)
  (key : module_name) : file_name FStar_Pervasives_Native.option=
  let uu___ = FStarC_SMap.try_find file_system_map key in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, FStar_Pervasives_Native.Some impl)
      -> FStar_Pervasives_Native.Some impl
  | uu___1 -> FStar_Pervasives_Native.None
let has_interface (file_system_map : files_for_module_name)
  (key : module_name) : Prims.bool=
  let uu___ = interface_of_internal file_system_map key in
  FStar_Pervasives_Native.uu___is_Some uu___
let has_implementation (file_system_map : files_for_module_name)
  (key : module_name) : Prims.bool=
  let uu___ = implementation_of_internal file_system_map key in
  FStar_Pervasives_Native.uu___is_Some uu___
let cache_file_name : Prims.string -> Prims.string=
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
                  let uu___7 =
                    FStarC_Errors_Msg.text "to be already checked." in
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStar_Pprint.doc_of_string mname) uu___7 in
                FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_Errors_Msg.text
                        "Found it in an unexpected location:" in
                    FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___8 (FStar_Pprint.doc_of_string path) in
                  let uu___8 =
                    let uu___9 = FStarC_Errors_Msg.text "instead of" in
                    FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___9 (FStar_Pprint.doc_of_string expected_cache_file) in
                  FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
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
  let memo1 f x =
    let uu___ = FStarC_SMap.try_find memo x in
    match uu___ with
    | FStar_Pervasives_Native.Some res -> res
    | FStar_Pervasives_Native.None ->
        let res = f x in (FStarC_SMap.add memo x res; res) in
  memo1 checked_file_and_exists_flag
let file_of_dep_aux (use_checked_file : Prims.bool)
  (file_system_map : files_for_module_name)
  (all_cmd_line_files : file_name Prims.list) (d : dependence) : file_name=
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
        (let uu___1 = FStarC_Options.dep () in
         FStar_Pervasives_Native.uu___is_None uu___1) &&
          (cmd_line_has_impl key) in
      if uu___
      then
        let uu___1 = FStarC_Options.expose_interfaces () in
        (if uu___1
         then
           let uu___2 =
             let uu___3 = implementation_of_internal file_system_map key in
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
                    let uu___8 = interface_of_internal file_system_map key in
                    FStarC_Option.must uu___8 in
                  let uu___8 =
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_list
                         FStarC_Class_Show.showable_string)
                      all_cmd_line_files in
                  FStarC_Format.fmt4
                    "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s.\n\n                                all_cmd_line_files=%s\n"
                    key uu___6 uu___7 uu___8 in
                FStarC_Errors_Msg.text uu___5 in
              let uu___5 =
                let uu___6 =
                  FStarC_Errors_Msg.text
                    "If you really want this behavior add the option '--expose_interfaces'." in
                [uu___6] in
              uu___4 :: uu___5 in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_MissingExposeInterfacesOption ()
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
let file_of_dep :
  files_for_module_name -> file_name Prims.list -> dependence -> file_name=
  file_of_dep_aux false
let files_of_dependences (fn : file_name)
  (file_system_map : files_for_module_name)
  (all_cmd_line_files : file_name Prims.list) (deps1 : dependence Prims.list)
  : file_name Prims.list=
  let uu___ =
    FStarC_List.map (file_of_dep file_system_map all_cmd_line_files) deps1 in
  FStarC_List.filter (fun k -> k <> fn) uu___
let dependences_of (file_system_map : files_for_module_name)
  (deps1 : dependence_graph) (all_cmd_line_files : file_name Prims.list)
  (fn : file_name) : file_name Prims.list=
  let uu___ = deps_try_find deps1 fn in
  match uu___ with
  | FStar_Pervasives_Native.None -> empty_dependences ()
  | FStar_Pervasives_Native.Some { edges = deps2; color = uu___1;_} ->
      files_of_dependences fn file_system_map all_cmd_line_files deps2
let print_graph (outc : FStarC_Util.out_channel) (fn : Prims.string)
  (graph : dependence_graph) (file_system_map : files_for_module_name)
  (cmd_lined_files : file_name Prims.list) : unit=
  (let uu___1 =
     let uu___2 = FStarC_Options.silent () in Prims.op_Negation uu___2 in
   if uu___1
   then
     (FStarC_Format.print1
        "A DOT-format graph has been dumped in the current directory as `%s`\n"
        fn;
      FStarC_Format.print1
        "With GraphViz installed, try: fdp -Tpng -odep.png %s\n" fn;
      FStarC_Format.print1 "Hint: cat %s | grep -v _ | grep -v prims\n" fn)
   else ());
  (let sb = FStarC_StringBuffer.create (Prims.of_int (10000)) in
   let pr str = let uu___1 = FStarC_StringBuffer.add str sb in () in
   pr "digraph {\n";
   (let uu___3 = let uu___4 = deps_keys graph in FStarC_List.unique uu___4 in
    FStarC_List.iter
      (fun k ->
         let deps1 =
           let uu___4 =
             let uu___5 = deps_try_find graph k in FStarC_Option.must uu___5 in
           uu___4.edges in
         FStarC_List.iter
           (fun dep ->
              let l = FStarC_Filepath.basename k in
              let r =
                let uu___4 = file_of_dep file_system_map cmd_lined_files dep in
                FStarC_Filepath.basename uu___4 in
              let uu___4 =
                let uu___5 =
                  FStarC_Options.should_be_already_cached
                    (module_name_of_dep dep) in
                Prims.op_Negation uu___5 in
              if uu___4
              then
                let uu___5 = FStarC_Format.fmt2 "  \"%s\" -> \"%s\"\n" l r in
                pr uu___5
              else ()) deps1) uu___3);
   pr "}\n";
   (let uu___4 = let uu___5 = FStarC_StringBuffer.contents sb in [uu___5] in
    FStarC_Util.fprint outc "%s" uu___4))
let safe_readdir_for_include (d : Prims.string) : Prims.string Prims.list=
  try (fun uu___ -> match () with | () -> FStarC_Filepath.readdir d) ()
  with | uu___ -> []
let build_inclusion_candidates_list (uu___ : unit) :
  (Prims.string * Prims.string) Prims.list=
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
let build_map
  (fs_map :
    (Prims.string FStar_Pervasives_Native.option * Prims.string
      FStar_Pervasives_Native.option) FStarC_SMap.t)
  (valid_ns_map : Prims.string Prims.list FStarC_SMap.t)
  (filenames : Prims.string Prims.list) : unit=
  let add_fs_entry key full_path =
    let uu___ = FStarC_SMap.try_find fs_map key in
    match uu___ with
    | FStar_Pervasives_Native.Some (intf, impl) ->
        let uu___1 = is_interface full_path in
        if uu___1
        then
          FStarC_SMap.add fs_map key
            ((FStar_Pervasives_Native.Some full_path), impl)
        else
          FStarC_SMap.add fs_map key
            (intf, (FStar_Pervasives_Native.Some full_path))
    | FStar_Pervasives_Native.None ->
        let uu___1 = is_interface full_path in
        if uu___1
        then
          FStarC_SMap.add fs_map key
            ((FStar_Pervasives_Native.Some full_path),
              FStar_Pervasives_Native.None)
        else
          FStarC_SMap.add fs_map key
            (FStar_Pervasives_Native.None,
              (FStar_Pervasives_Native.Some full_path)) in
  let add_ns_entry key full_path =
    let uu___ = namespace_of_module key in
    match uu___ with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some ns ->
        let ns1 = FStarC_Ident.string_of_lid ns in
        let uu___1 = FStarC_SMap.try_find valid_ns_map ns1 in
        (match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStarC_SMap.add valid_ns_map ns1 [key]
         | FStar_Pervasives_Native.Some keys ->
             FStarC_SMap.add valid_ns_map ns1 (key :: keys)) in
  let add_entry key full_path =
    add_fs_entry key full_path; add_ns_entry key full_path in
  (let uu___1 = build_inclusion_candidates_list () in
   FStarC_List.iter
     (fun uu___2 ->
        match uu___2 with
        | (longname, full_path) ->
            add_entry (FStarC_String.lowercase longname) full_path) uu___1);
  FStarC_List.iter
    (fun f -> let uu___1 = lowercase_module_name f in add_entry uu___1 f)
    filenames
let is_valid_namespace (deps1 : deps) (ns : FStarC_Ident.lident) :
  Prims.bool=
  let res =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid ns in
        FStarC_String.lowercase uu___2 in
      FStarC_SMap.try_find deps1.valid_namespaces uu___1 in
    FStar_Pervasives_Native.uu___is_Some uu___ in
  if Prims.op_Negation res
  then
    (let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident ns in
     let uu___2 =
       let uu___3 = FStarC_SMap.keys deps1.valid_namespaces in
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
         uu___3 in
     FStarC_Format.print2
       "Could not resolve namespace %s\n valid namespaces are %s\n" uu___1
       uu___2)
  else ();
  res
let interface_of (deps1 : deps) (key : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  (let uu___1 =
     let uu___2 = FStarC_SMap.keys deps1.file_system_map in
     Prims.uu___is_Nil uu___2 in
   if uu___1
   then
     build_map deps1.file_system_map deps1.valid_namespaces
       deps1.cmd_line_files
   else ());
  interface_of_internal deps1.file_system_map key
let implementation_of (deps1 : deps) (key : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  (let uu___1 =
     let uu___2 = FStarC_SMap.keys deps1.file_system_map in
     Prims.uu___is_Nil uu___2 in
   if uu___1
   then
     build_map deps1.file_system_map deps1.valid_namespaces
       deps1.cmd_line_files
   else ());
  implementation_of_internal deps1.file_system_map key
let string_of_lid (l : FStarC_Ident.lident) (last : Prims.bool) :
  Prims.string=
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
let lowercase_join_longident (l : FStarC_Ident.lident) (last : Prims.bool) :
  Prims.string=
  let uu___ = string_of_lid l last in FStarC_String.lowercase uu___
let namespace_of_lid (l : FStarC_Ident.lident) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Ident.ns_of_lid l in
    FStarC_List.map FStarC_Ident.string_of_id uu___1 in
  FStarC_String.concat "_" uu___
let check_module_declaration_against_filename (lid : FStarC_Ident.lident)
  (filename : Prims.string) : unit=
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
let uu___is_Exit (projectee : Prims.exn) : Prims.bool=
  match projectee with | Exit -> true | uu___ -> false
let dep_subsumed_by (d : dependence) (d' : dependence) : Prims.bool=
  match (d, d') with
  | (PreferInterface l', FriendImplementation l) -> l = l'
  | uu___ -> d = d'
let warned_about :
  intf_and_impl FStar_Pervasives_Native.option Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let enter_namespace (original_map : files_for_module_name)
  (working_map : files_for_module_name) (sprefix : Prims.string)
  (implicit_open : Prims.bool) : Prims.bool=
  let found = FStarC_Effect.mk_ref false in
  let sprefix1 = Prims.strcat sprefix "." in
  let suffix_exists mopt =
    match mopt with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some (intf, impl) ->
        (FStar_Pervasives_Native.uu___is_Some intf) ||
          (FStar_Pervasives_Native.uu___is_Some impl) in
  FStarC_SMap.iter original_map
    (fun k _fn ->
       if FStarC_Util.starts_with k sprefix1
       then
         let suffix =
           FStarC_String.substring k (FStarC_String.length sprefix1)
             ((FStarC_String.length k) - (FStarC_String.length sprefix1)) in
         ((let suffix_filename = FStarC_SMap.try_find original_map suffix in
           let uu___2 =
             (implicit_open && (suffix_exists suffix_filename)) &&
               (let uu___3 =
                  let uu___4 = FStarC_Effect.op_Bang warned_about in
                  FStarC_List.mem suffix_filename uu___4 in
                Prims.op_Negation uu___3) in
           if uu___2
           then
             let str =
               let uu___3 = FStarC_Option.must suffix_filename in
               intf_and_impl_to_string uu___3 in
             ((let uu___4 =
                 let uu___5 = FStarC_Effect.op_Bang warned_about in
                 suffix_filename :: uu___5 in
               FStarC_Effect.op_Colon_Equals warned_about uu___4);
              (let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       FStarC_Errors_Msg.text "Implicitly opening namespace" in
                     let uu___8 =
                       let uu___9 =
                         let uu___10 =
                           FStarC_Errors_Msg.text "shadows module" in
                         let uu___11 =
                           let uu___12 =
                             let uu___13 = FStarC_Errors_Msg.text "in file" in
                             [uu___13;
                             FStar_Pprint.op_Hat_Hat
                               (FStar_Pprint.dquotes
                                  (FStar_Pprint.doc_of_string str))
                               FStar_Pprint.dot] in
                           (FStar_Pprint.squotes
                              (FStar_Pprint.doc_of_string suffix))
                             :: uu___12 in
                         uu___10 :: uu___11 in
                       (FStar_Pprint.squotes
                          (FStar_Pprint.doc_of_string sprefix1))
                         :: uu___9 in
                     uu___7 :: uu___8 in
                   FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
                     uu___6 in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = FStarC_Errors_Msg.text "Rename" in
                     let uu___9 =
                       let uu___10 =
                         FStarC_Errors_Msg.text "to avoid conflicts." in
                       FStar_Pprint.op_Hat_Slash_Hat
                         (FStar_Pprint.dquotes
                            (FStar_Pprint.doc_of_string str)) uu___10 in
                     FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                   [uu___7] in
                 uu___5 :: uu___6 in
               FStarC_Errors.log_issue0
                 FStarC_Errors_Codes.Warning_UnexpectedFile ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___4)))
           else ());
          (let filename =
             let uu___2 = FStarC_SMap.try_find original_map k in
             FStarC_Option.must uu___2 in
           FStarC_SMap.add working_map suffix filename;
           FStarC_Effect.op_Colon_Equals found true))
       else ());
  FStarC_Effect.op_Bang found
let prelude_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_str "FStar.Prelude"
let prelude : (open_kind * FStarC_Ident.lid) Prims.list=
  [(Open_namespace, FStarC_Parser_Const.fstar_ns_lid);
  (Open_module, prelude_lid)]
let peek_past_interfaces (uu___ : unit) : Prims.bool=
  let uu___1 =
    (FStarC_Options_Ext.enabled "dep_minimal") || (fly_deps_enabled ()) in
  if uu___1
  then false
  else (let uu___3 = FStarC_Options.ide () in Prims.op_Negation uu___3)
let collect_module_or_decls (filename : Prims.string)
  (m :
    (FStarC_Parser_AST.modul, FStarC_Parser_AST.decl Prims.list)
      FStar_Pervasives.either)
  : parsing_data=
  let num_of_toplevelmods = FStarC_Effect.mk_ref Prims.int_zero in
  let pd = FStarC_Effect.mk_ref empty_parsing_data in
  let add_to_parsing_data elt =
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = FStarC_Effect.op_Bang pd in uu___3.elts in
        FStarC_List.existsML (fun e -> parsing_data_elt_eq e elt) uu___2 in
      Prims.op_Negation uu___1 in
    if uu___
    then
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang pd in
        let uu___3 =
          let uu___4 = let uu___5 = FStarC_Effect.op_Bang pd in uu___5.elts in
          elt :: uu___4 in
        { elts = uu___3; no_prelude = (uu___2.no_prelude) } in
      FStarC_Effect.op_Colon_Equals pd uu___1
    else () in
  let set_no_prelude b =
    let uu___ =
      let uu___1 = FStarC_Effect.op_Bang pd in
      { elts = (uu___1.elts); no_prelude = b } in
    FStarC_Effect.op_Colon_Equals pd uu___ in
  let rec go uu___ =
    match uu___ with
    | FStar_Pervasives.Inl (FStarC_Parser_AST.Module
        { FStarC_Parser_AST.no_prelude = no_prelude;
          FStarC_Parser_AST.mname = mname; FStarC_Parser_AST.decls = decls;_})
        ->
        (set_no_prelude no_prelude;
         add_to_parsing_data (P_begin_module mname);
         collect_decls decls)
    | FStar_Pervasives.Inl (FStarC_Parser_AST.Interface
        { FStarC_Parser_AST.no_prelude1 = no_prelude;
          FStarC_Parser_AST.mname1 = mname; FStarC_Parser_AST.decls1 = decls;
          FStarC_Parser_AST.admitted = uu___1;_})
        ->
        (set_no_prelude no_prelude;
         add_to_parsing_data (P_begin_module mname);
         collect_decls decls)
    | FStar_Pervasives.Inr decls ->
        (set_no_prelude true; collect_decls decls)
  and collect_decls decls =
    FStarC_List.iter
      (fun x ->
         collect_decl x.FStarC_Parser_AST.d;
         FStarC_List.iter collect_term x.FStarC_Parser_AST.attrs;
         if
           FStarC_List.contains FStarC_Parser_AST.Inline_for_extraction
             x.FStarC_Parser_AST.quals
         then add_to_parsing_data P_inline_for_extraction
         else ()) decls
  and collect_decl d =
    match d with
    | FStarC_Parser_AST.Include (lid, uu___) ->
        add_to_parsing_data (P_open (false, lid))
    | FStarC_Parser_AST.Open (lid, uu___) ->
        add_to_parsing_data (P_open (false, lid))
    | FStarC_Parser_AST.Friend lid ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = lowercase_join_longident lid true in
              FStarC_Ident.lid_of_str uu___3 in
            (true, uu___2) in
          P_dep uu___1 in
        add_to_parsing_data uu___
    | FStarC_Parser_AST.ModuleAbbrev (ident, lid) ->
        add_to_parsing_data (P_alias (ident, lid))
    | FStarC_Parser_AST.TopLevelLet (uu___, patterms) ->
        FStarC_List.iter
          (fun uu___1 ->
             match uu___1 with
             | (pat, t) -> (collect_pattern pat; collect_term t)) patterms
    | FStarC_Parser_AST.Splice (uu___, uu___1, t) -> collect_term t
    | FStarC_Parser_AST.Assume (uu___, t) -> collect_term t
    | FStarC_Parser_AST.SubEffect
        { FStarC_Parser_AST.msource = uu___;
          FStarC_Parser_AST.mdest = uu___1;
          FStarC_Parser_AST.lift_op = FStarC_Parser_AST.NonReifiableLift t;
          FStarC_Parser_AST.braced = uu___2;_}
        -> collect_term t
    | FStarC_Parser_AST.SubEffect
        { FStarC_Parser_AST.msource = uu___;
          FStarC_Parser_AST.mdest = uu___1;
          FStarC_Parser_AST.lift_op = FStarC_Parser_AST.LiftForFree t;
          FStarC_Parser_AST.braced = uu___2;_}
        -> collect_term t
    | FStarC_Parser_AST.Val (uu___, t) -> collect_term t
    | FStarC_Parser_AST.SubEffect
        { FStarC_Parser_AST.msource = uu___;
          FStarC_Parser_AST.mdest = uu___1;
          FStarC_Parser_AST.lift_op = FStarC_Parser_AST.ReifiableLift
            (t0, t1);
          FStarC_Parser_AST.braced = uu___2;_}
        -> (collect_term t0; collect_term t1)
    | FStarC_Parser_AST.Tycon (uu___, tc, ts) ->
        (if tc
         then add_to_parsing_data (P_lid FStarC_Parser_Const.tcclass_lid)
         else ();
         FStarC_List.iter collect_tycon ts)
    | FStarC_Parser_AST.Exception (uu___, t) ->
        FStarC_Option.iter collect_term t
    | FStarC_Parser_AST.NewEffect ed -> collect_effect_decl ed
    | FStarC_Parser_AST.LayeredEffect ed -> collect_effect_decl ed
    | FStarC_Parser_AST.Polymonadic_bind (uu___, uu___1, uu___2, t) ->
        collect_term t
    | FStarC_Parser_AST.Polymonadic_subcomp (uu___, uu___1, t) ->
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
    | FStarC_Parser_AST.UseLangDecls uu___ -> ()
    | FStarC_Parser_AST.Pragma uu___ -> ()
    | FStarC_Parser_AST.DeclSyntaxExtension uu___ -> ()
    | FStarC_Parser_AST.Unparseable -> ()
    | FStarC_Parser_AST.TopLevelModule lid ->
        (FStarC_Util.incr num_of_toplevelmods;
         (let uu___1 =
            let uu___2 = FStarC_Effect.op_Bang num_of_toplevelmods in
            uu___2 > Prims.int_one in
          if uu___1
          then
            let uu___2 =
              let uu___3 = string_of_lid lid true in
              FStarC_Format.fmt1
                "Automatic dependency analysis demands one module per file (module %s not supported)"
                uu___3 in
            FStarC_Errors.raise_error FStarC_Ident.hasrange_lident lid
              FStarC_Errors_Codes.Fatal_OneModulePerFile ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2)
          else ()))
  and collect_tycon uu___ =
    match uu___ with
    | FStarC_Parser_AST.TyconAbstract (uu___1, binders, k) ->
        (collect_binders binders; FStarC_Option.iter collect_term k)
    | FStarC_Parser_AST.TyconAbbrev (uu___1, binders, k, t) ->
        (collect_binders binders;
         FStarC_Option.iter collect_term k;
         collect_term t)
    | FStarC_Parser_AST.TyconRecord (uu___1, binders, k, uu___2, identterms)
        ->
        (collect_binders binders;
         FStarC_Option.iter collect_term k;
         collect_tycon_record identterms)
    | FStarC_Parser_AST.TyconVariant (uu___1, binders, k, identterms) ->
        (collect_binders binders;
         FStarC_Option.iter collect_term k;
         (let uu___4 =
            FStarC_List.filter_map
              FStar_Pervasives_Native.__proj__Mktuple3__item___2 identterms in
          FStarC_List.iter
            (fun uu___5 ->
               match uu___5 with
               | FStarC_Parser_AST.VpOfNotation t -> collect_term t
               | FStarC_Parser_AST.VpArbitrary t -> collect_term t
               | FStarC_Parser_AST.VpRecord (record, t) ->
                   (collect_tycon_record record;
                    FStarC_Option.iter collect_term t)) uu___4))
  and collect_tycon_record r =
    FStarC_List.iter
      (fun uu___ ->
         match uu___ with
         | (uu___1, aq, attrs, t) ->
             (collect_aqual aq;
              FStarC_List.iter collect_term attrs;
              collect_term t)) r
  and collect_effect_decl uu___ =
    match uu___ with
    | FStarC_Parser_AST.DefineEffect (uu___1, binders, t, decls) ->
        (collect_binders binders; collect_term t; collect_decls decls)
    | FStarC_Parser_AST.RedefineEffect (uu___1, binders, t) ->
        (collect_binders binders; collect_term t)
  and collect_binders binders = FStarC_List.iter collect_binder binders
  and collect_binder b =
    collect_aqual b.FStarC_Parser_AST.aqual;
    FStarC_List.iter collect_term b.FStarC_Parser_AST.battributes;
    (match b with
     | { FStarC_Parser_AST.b = FStarC_Parser_AST.Annotated (uu___2, t);
         FStarC_Parser_AST.brange = uu___3;
         FStarC_Parser_AST.blevel = uu___4; FStarC_Parser_AST.aqual = uu___5;
         FStarC_Parser_AST.battributes = uu___6;_} -> collect_term t
     | { FStarC_Parser_AST.b = FStarC_Parser_AST.NoName t;
         FStarC_Parser_AST.brange = uu___2;
         FStarC_Parser_AST.blevel = uu___3; FStarC_Parser_AST.aqual = uu___4;
         FStarC_Parser_AST.battributes = uu___5;_} -> collect_term t
     | uu___2 -> ())
  and collect_aqual uu___ =
    match uu___ with
    | FStar_Pervasives_Native.Some (FStarC_Parser_AST.Meta t) ->
        collect_term t
    | FStar_Pervasives_Native.Some (FStarC_Parser_AST.TypeClassArg) ->
        add_to_parsing_data (P_lid FStarC_Parser_Const.tcresolve_lid)
    | uu___1 -> ()
  and collect_term t = collect_term' t.FStarC_Parser_AST.tm
  and collect_constant uu___ =
    match uu___ with
    | FStarC_Const.Const_int
        (uu___1, FStar_Pervasives_Native.Some
         (FStarC_Const.Unsigned, FStarC_Const.Sizet))
        ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Ident.lid_of_str "fstar.sizeT" in
            (false, uu___4) in
          P_dep uu___3 in
        add_to_parsing_data uu___2
    | FStarC_Const.Const_int
        (uu___1, FStar_Pervasives_Native.Some (signedness, width)) ->
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
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Format.fmt2 "fstar.%sint%s" u w in
              FStarC_Ident.lid_of_str uu___5 in
            (false, uu___4) in
          P_dep uu___3 in
        add_to_parsing_data uu___2
    | FStarC_Const.Const_char uu___1 ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Ident.lid_of_str "fstar.char" in
            (false, uu___4) in
          P_dep uu___3 in
        add_to_parsing_data uu___2
    | FStarC_Const.Const_range_of ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Ident.lid_of_str "fstar.range" in
            (false, uu___3) in
          P_dep uu___2 in
        add_to_parsing_data uu___1
    | FStarC_Const.Const_set_range_of ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Ident.lid_of_str "fstar.range" in
            (false, uu___3) in
          P_dep uu___2 in
        add_to_parsing_data uu___1
    | FStarC_Const.Const_real uu___1 ->
        let mm = maybe_module_name_of_file filename in
        if mm <> (FStar_Pervasives_Native.Some "FStar.Real")
        then
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "fstar.real" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2
        else ()
    | uu___1 -> ()
  and collect_term' uu___ =
    match uu___ with
    | FStarC_Parser_AST.Wild -> ()
    | FStarC_Parser_AST.Const c -> collect_constant c
    | FStarC_Parser_AST.Op (uu___1, ts) -> FStarC_List.iter collect_term ts
    | FStarC_Parser_AST.Uvar uu___1 -> ()
    | FStarC_Parser_AST.Var lid -> add_to_parsing_data (P_lid lid)
    | FStarC_Parser_AST.Projector (lid, uu___1) ->
        add_to_parsing_data (P_lid lid)
    | FStarC_Parser_AST.Discrim lid -> add_to_parsing_data (P_lid lid)
    | FStarC_Parser_AST.Name lid -> add_to_parsing_data (P_lid lid)
    | FStarC_Parser_AST.Construct (lid, termimps) ->
        (add_to_parsing_data (P_lid lid);
         FStarC_List.iter
           (fun uu___2 -> match uu___2 with | (t, uu___3) -> collect_term t)
           termimps)
    | FStarC_Parser_AST.Function (branches, uu___1) ->
        collect_branches branches
    | FStarC_Parser_AST.Abs (pats, t) ->
        (collect_patterns pats; collect_term t)
    | FStarC_Parser_AST.App (t1, t2, uu___1) ->
        (collect_term t1; collect_term t2)
    | FStarC_Parser_AST.Let (uu___1, patterms, t) ->
        (FStarC_List.iter
           (fun uu___3 ->
              match uu___3 with
              | (attrs_opt, (pat, t1)) ->
                  ((let uu___5 =
                      FStarC_Option.map (FStarC_List.iter collect_term)
                        attrs_opt in
                    ());
                   collect_pattern pat;
                   collect_term t1)) patterms;
         collect_term t)
    | FStarC_Parser_AST.LetOperator (lets, body) ->
        (FStarC_List.iter
           (fun uu___2 ->
              match uu___2 with
              | (ident, pat, def) -> (collect_pattern pat; collect_term def))
           lets;
         collect_term body)
    | FStarC_Parser_AST.LetOpen (lid, t) ->
        (add_to_parsing_data (P_open (true, lid)); collect_term t)
    | FStarC_Parser_AST.LetOpenRecord (r, rty, e) ->
        (collect_term r; collect_term rty; collect_term e)
    | FStarC_Parser_AST.Bind (uu___1, t1, t2) ->
        (collect_term t1; collect_term t2)
    | FStarC_Parser_AST.Seq (t1, t2) -> (collect_term t1; collect_term t2)
    | FStarC_Parser_AST.If (t1, uu___1, ret_opt, t2, t3) ->
        (collect_term t1;
         (match ret_opt with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some (uu___4, ret, uu___5) ->
              collect_term ret);
         collect_term t2;
         collect_term t3)
    | FStarC_Parser_AST.Match (t, uu___1, ret_opt, bs) ->
        (collect_term t;
         (match ret_opt with
          | FStar_Pervasives_Native.None -> ()
          | FStar_Pervasives_Native.Some (uu___4, ret, uu___5) ->
              collect_term ret);
         collect_branches bs)
    | FStarC_Parser_AST.TryWith (t, bs) ->
        (collect_term t; collect_branches bs)
    | FStarC_Parser_AST.Ascribed
        (t1, t2, FStar_Pervasives_Native.None, uu___1) ->
        (collect_term t1; collect_term t2)
    | FStarC_Parser_AST.Ascribed
        (t1, t2, FStar_Pervasives_Native.Some tac, uu___1) ->
        (collect_term t1; collect_term t2; collect_term tac)
    | FStarC_Parser_AST.Record (t, idterms) ->
        (FStarC_Option.iter collect_term t;
         FStarC_List.iter
           (fun uu___2 ->
              match uu___2 with
              | (fn, t1) -> (collect_fieldname fn; collect_term t1)) idterms)
    | FStarC_Parser_AST.Project (t, f) ->
        (collect_term t; collect_fieldname f)
    | FStarC_Parser_AST.Product (binders, t) ->
        (collect_binders binders; collect_term t)
    | FStarC_Parser_AST.Sum (binders, t) ->
        (FStarC_List.iter
           (fun uu___2 ->
              match uu___2 with
              | FStar_Pervasives.Inl b -> collect_binder b
              | FStar_Pervasives.Inr t1 -> collect_term t1) binders;
         collect_term t)
    | FStarC_Parser_AST.QForall (binders, (uu___1, ts), t) ->
        (collect_binders binders;
         FStarC_List.iter (FStarC_List.iter collect_term) ts;
         collect_term t)
    | FStarC_Parser_AST.QExists (binders, (uu___1, ts), t) ->
        (collect_binders binders;
         FStarC_List.iter (FStarC_List.iter collect_term) ts;
         collect_term t)
    | FStarC_Parser_AST.QuantOp (uu___1, binders, (uu___2, ts), t) ->
        (collect_binders binders;
         FStarC_List.iter (FStarC_List.iter collect_term) ts;
         collect_term t)
    | FStarC_Parser_AST.Refine (binder, t) ->
        (collect_binder binder; collect_term t)
    | FStarC_Parser_AST.NamedTyp (uu___1, t) -> collect_term t
    | FStarC_Parser_AST.Paren t -> collect_term t
    | FStarC_Parser_AST.Requires t -> collect_term t
    | FStarC_Parser_AST.Ensures t -> collect_term t
    | FStarC_Parser_AST.Labeled (t, uu___1, uu___2) -> collect_term t
    | FStarC_Parser_AST.LexList l -> FStarC_List.iter collect_term l
    | FStarC_Parser_AST.WFOrder (t1, t2) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.WellFounded" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term t1;
         collect_term t2)
    | FStarC_Parser_AST.Decreases t -> collect_term t
    | FStarC_Parser_AST.Quote (t, uu___1) -> collect_term t
    | FStarC_Parser_AST.Antiquote t -> collect_term t
    | FStarC_Parser_AST.VQuote t -> collect_term t
    | FStarC_Parser_AST.Attributes cattributes ->
        FStarC_List.iter collect_term cattributes
    | FStarC_Parser_AST.CalcProof (rel, init, steps) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Calc" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term rel;
         collect_term init;
         FStarC_List.iter
           (fun uu___4 ->
              match uu___4 with
              | FStarC_Parser_AST.CalcStep (rel1, just, next) ->
                  (collect_term rel1; collect_term just; collect_term next))
           steps)
    | FStarC_Parser_AST.IntroForall (bs, p, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_binders bs;
         collect_term p;
         collect_term e)
    | FStarC_Parser_AST.IntroExists (bs, t, vs, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_binders bs;
         collect_term t;
         FStarC_List.iter collect_term vs;
         collect_term e)
    | FStarC_Parser_AST.IntroImplies (p, q, x, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term p;
         collect_term q;
         collect_binder x;
         collect_term e)
    | FStarC_Parser_AST.IntroOr (b, p, q, r) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term p;
         collect_term q;
         collect_term r)
    | FStarC_Parser_AST.IntroAnd (p, q, r, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term p;
         collect_term q;
         collect_term r;
         collect_term e)
    | FStarC_Parser_AST.ElimForall (bs, p, vs) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_binders bs;
         collect_term p;
         FStarC_List.iter collect_term vs)
    | FStarC_Parser_AST.ElimExists (bs, p, q, b, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_binders bs;
         collect_term p;
         collect_term q;
         collect_binder b;
         collect_term e)
    | FStarC_Parser_AST.ElimImplies (p, q, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term p;
         collect_term q;
         collect_term e)
    | FStarC_Parser_AST.ElimAnd (p, q, r, x, y, e) ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term p;
         collect_term q;
         collect_term r;
         collect_binder x;
         collect_binder y;
         collect_term e)
    | FStarC_Parser_AST.ElimOr (p, q, r, x, e, y, e') ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Classical.Sugar" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         collect_term p;
         collect_term q;
         collect_term r;
         collect_binder x;
         collect_binder y;
         collect_term e;
         collect_term e')
    | FStarC_Parser_AST.ListLiteral ts -> FStarC_List.iter collect_term ts
    | FStarC_Parser_AST.SeqLiteral ts ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Ident.lid_of_str "FStar.Seq.Base" in
              (false, uu___4) in
            P_dep uu___3 in
          add_to_parsing_data uu___2);
         FStarC_List.iter collect_term ts)
  and collect_patterns ps = FStarC_List.iter collect_pattern ps
  and collect_pattern p = collect_pattern' p.FStarC_Parser_AST.pat
  and collect_pattern' uu___ =
    match uu___ with
    | FStarC_Parser_AST.PatVar (uu___1, aqual, attrs) ->
        (collect_aqual aqual; FStarC_List.iter collect_term attrs)
    | FStarC_Parser_AST.PatWild (aqual, attrs) ->
        (collect_aqual aqual; FStarC_List.iter collect_term attrs)
    | FStarC_Parser_AST.PatRest -> ()
    | FStarC_Parser_AST.PatOp uu___1 -> ()
    | FStarC_Parser_AST.PatConst uu___1 -> ()
    | FStarC_Parser_AST.PatVQuote t -> collect_term t
    | FStarC_Parser_AST.PatApp (p, ps) ->
        (collect_pattern p; collect_patterns ps)
    | FStarC_Parser_AST.PatName lid -> add_to_parsing_data (P_lid lid)
    | FStarC_Parser_AST.PatList ps -> collect_patterns ps
    | FStarC_Parser_AST.PatOr ps -> collect_patterns ps
    | FStarC_Parser_AST.PatTuple (ps, uu___1) -> collect_patterns ps
    | FStarC_Parser_AST.PatRecord lidpats ->
        FStarC_List.iter
          (fun uu___1 -> match uu___1 with | (uu___2, p) -> collect_pattern p)
          lidpats
    | FStarC_Parser_AST.PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
        (collect_pattern p; collect_term t)
    | FStarC_Parser_AST.PatAscribed
        (p, (t, FStar_Pervasives_Native.Some tac)) ->
        (collect_pattern p; collect_term t; collect_term tac)
  and collect_branches bs = FStarC_List.iter collect_branch bs
  and collect_branch uu___ =
    match uu___ with
    | (pat, t1, t2) ->
        (collect_pattern pat;
         FStarC_Option.iter collect_term t1;
         collect_term t2)
  and collect_fieldname fn =
    let uu___ = let uu___1 = FStarC_Ident.nsstr fn in uu___1 <> "" in
    if uu___
    then
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Ident.ns_of_lid fn in
            FStarC_Ident.lid_of_ids uu___4 in
          (false, uu___3) in
        P_dep uu___2 in
      add_to_parsing_data uu___1
    else () in
  go m; FStarC_Effect.op_Bang pd
let maybe_use_interface (file_system_map : files_for_module_name)
  (file_name1 : Prims.string) : dependence Prims.list=
  let module_name1 = lowercase_module_name file_name1 in
  let uu___ =
    (is_implementation file_name1) &&
      (has_interface file_system_map module_name1) in
  if uu___ then [UseInterface module_name1] else []
let deps_from_parsing_data (pd : parsing_data)
  (original_map : files_for_module_name) (filename : Prims.string) :
  (dependence Prims.list * Prims.bool * dependence Prims.list)=
  let deps1 = FStarC_Effect.mk_ref [] in
  let has_inline_for_extraction = FStarC_Effect.mk_ref false in
  let mname = lowercase_module_name filename in
  let mo_roots =
    let uu___ =
      ((is_interface filename) && (has_implementation original_map mname)) &&
        (peek_past_interfaces ()) in
    if uu___ then [UseImplementation mname] else [] in
  let auto_open =
    let open_module_ns =
      let uu___ = namespace_of_module mname in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some ns ->
          [P_implicit_open_module_or_namespace (Open_namespace, ns)] in
    if pd.no_prelude
    then open_module_ns
    else
      (let uu___1 =
         FStarC_List.map
           (fun uu___2 -> match uu___2 with | (k, l) -> P_open (false, l))
           prelude in
       FStarC_List.op_At uu___1 open_module_ns) in
  let working_map = FStarC_SMap.copy original_map in
  let set_interface_inlining uu___ =
    let uu___1 = is_interface filename in
    if uu___1
    then FStarC_Effect.op_Colon_Equals has_inline_for_extraction true
    else () in
  let add_dep d =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang deps1 in
        FStarC_List.existsML (dep_subsumed_by d) uu___2 in
      Prims.op_Negation uu___1 in
    if uu___
    then
      let uu___1 = let uu___2 = FStarC_Effect.op_Bang deps1 in d :: uu___2 in
      FStarC_Effect.op_Colon_Equals deps1 uu___1
    else () in
  let dep_edge module_name1 is_friend =
    if is_friend
    then FriendImplementation module_name1
    else PreferInterface module_name1 in
  let add_dependence_edge original_or_working_map lid is_friend =
    let key = lowercase_join_longident lid true in
    (let uu___1 = FStarC_Effect.op_Bang dbg in
     if uu___1 then FStarC_Format.print1 "Resolving %s ..\n" key else ());
    (let uu___1 = resolve_module_name original_or_working_map key in
     match uu___1 with
     | FStar_Pervasives_Native.Some module_name1 ->
         ((let uu___3 = is_friend && (fly_deps_enabled ()) in
           if uu___3
           then
             let already_depends_on_iface =
               let uu___4 = FStarC_Effect.op_Bang deps1 in
               FStarC_List.existsb
                 (fun uu___5 ->
                    match uu___5 with
                    | PreferInterface mname' -> mname' = mname
                    | uu___6 -> false) uu___4 in
             (if already_depends_on_iface
              then
                let uu___4 = FStarC_Ident.range_of_lid lid in
                let uu___5 =
                  let uu___6 =
                    FStarC_Errors_Msg.text
                      "Friend dependences must be declared as the first dependence on a module." in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        FStarC_Format.fmt1
                          "A non-friend dependence was already found on module %s."
                          module_name1 in
                      FStarC_Errors_Msg.text uu___9 in
                    [uu___8] in
                  uu___6 :: uu___7 in
                FStarC_Errors.raise_error
                  FStarC_Class_HasRange.hasRange_range uu___4
                  FStarC_Errors_Codes.Fatal_CyclicDependence ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic uu___5)
              else ())
           else ());
          add_dep (dep_edge module_name1 is_friend);
          true)
     | uu___2 -> false) in
  let record_open_module let_open lid =
    let uu___ =
      (let_open && (add_dependence_edge working_map lid false)) ||
        ((Prims.op_Negation let_open) &&
           (add_dependence_edge original_map lid false)) in
    if uu___
    then true
    else
      (if let_open
       then
         (let uu___3 =
            let uu___4 = string_of_lid lid true in
            FStarC_Format.fmt1 "Module not found: %s" uu___4 in
          FStarC_Errors.log_issue FStarC_Ident.hasrange_lident lid
            FStarC_Errors_Codes.Warning_ModuleOrFileNotFoundWarning ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___3))
       else ();
       false) in
  let record_open_namespace lid implicit_open =
    let key = lowercase_join_longident lid true in
    let r = enter_namespace original_map working_map key implicit_open in
    if (Prims.op_Negation r) && (Prims.op_Negation implicit_open)
    then
      let uu___ =
        let uu___1 = string_of_lid lid true in
        FStarC_Format.fmt1
          "No modules in namespace %s and no file with that name either"
          uu___1 in
      FStarC_Errors.log_issue FStarC_Ident.hasrange_lident lid
        FStarC_Errors_Codes.Warning_ModuleOrFileNotFoundWarning ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
    else () in
  let record_open let_open lid =
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
         | Open_module -> let uu___1 = record_open_module false lid in ()) in
  let record_module_alias ident lid =
    let key =
      let uu___ = FStarC_Ident.string_of_id ident in
      FStarC_String.lowercase uu___ in
    let alias = lowercase_join_longident lid true in
    let uu___ = FStarC_SMap.try_find original_map alias in
    match uu___ with
    | FStar_Pervasives_Native.Some deps_of_aliased_module ->
        (FStarC_SMap.add working_map key deps_of_aliased_module;
         (let uu___3 =
            let uu___4 = lowercase_join_longident lid true in
            dep_edge uu___4 false in
          add_dep uu___3);
         true)
    | FStar_Pervasives_Native.None ->
        ((let uu___2 =
            FStarC_Format.fmt1 "module not found in search path: %s" alias in
          FStarC_Errors.log_issue FStarC_Ident.hasrange_lident lid
            FStarC_Errors_Codes.Warning_ModuleOrFileNotFoundWarning ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         false) in
  let add_dep_on_module module_name1 is_friend =
    (let uu___1 = FStarC_Effect.op_Bang dbg in
     if uu___1
     then
       let uu___2 =
         FStarC_Class_Show.show FStarC_Ident.showable_lident module_name1 in
       FStarC_Format.print1 "Adding dep on module %s ..\n" uu___2
     else ());
    (let uu___1 = add_dependence_edge working_map module_name1 is_friend in
     if uu___1
     then ()
     else
       (let uu___3 = FStarC_Effect.op_Bang dbg in
        if uu___3
        then
          let uu___4 =
            let uu___5 =
              FStarC_Class_Show.show FStarC_Ident.showable_lident
                module_name1 in
            FStarC_Format.fmt1 "Unbound module reference %s" uu___5 in
          FStarC_Errors.log_issue FStarC_Ident.hasrange_lident module_name1
            FStarC_Errors_Codes.Warning_UnboundModuleReference ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___4)
        else ())) in
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
        let uu___2 = FStarC_Ident.ns_of_lid lid in FStarC_List.length uu___2 in
      uu___1 > Prims.int_zero in
    if uu___
    then
      ((let uu___2 = FStarC_Effect.op_Bang dbg in
        if uu___2
        then
          let uu___3 =
            FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
          FStarC_Format.print1 "Begin module %s ..\n" uu___3
        else ());
       (let uu___2 =
          let uu___3 =
            let uu___4 = namespace_of_lid lid in
            FStarC_String.lowercase uu___4 in
          enter_namespace original_map working_map uu___3 in
        ()))
    else () in
  let elts =
    let uu___ = (fly_deps_enabled ()) && pd.no_prelude in
    if uu___
    then
      match pd.elts with
      | (P_open (false, fstar_lid))::(P_open (false, prelude_lid'))::rest
          when
          (FStarC_Ident.lid_equals FStarC_Parser_Const.fstar_ns_lid fstar_lid)
            && (FStarC_Ident.lid_equals prelude_lid prelude_lid')
          ->
          FStarC_List.op_At ((P_open (false, fstar_lid)) ::
            (P_open (false, prelude_lid)) :: auto_open) rest
      | uu___1 -> FStarC_List.op_At auto_open pd.elts
    else FStarC_List.op_At auto_open pd.elts in
  FStarC_List.iter
    (fun elt ->
       match elt with
       | P_begin_module lid -> begin_module lid
       | P_open (b, lid) -> record_open b lid
       | P_implicit_open_module_or_namespace (k, lid) ->
           ((let uu___2 = FStarC_Effect.op_Bang dbg in
             if uu___2
             then
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
               FStarC_Format.print1 "Implicitly opening %s ..\n" uu___3
             else ());
            record_implicit_open_module_or_namespace (lid, k))
       | P_dep (b, lid) -> add_dep_on_module lid b
       | P_alias (id, lid) -> let uu___1 = record_module_alias id lid in ()
       | P_lid lid -> record_lid lid
       | P_inline_for_extraction -> set_interface_inlining ()) elts;
  (let uu___1 = FStarC_Effect.op_Bang deps1 in
   let uu___2 = FStarC_Effect.op_Bang has_inline_for_extraction in
   (uu___1, uu___2, mo_roots))
let collect_one (original_map : files_for_module_name)
  (filename : Prims.string)
  (get_parsing_data_from_cache :
    Prims.string -> parsing_data FStar_Pervasives_Native.option)
  :
  (parsing_data * dependence Prims.list * Prims.bool * dependence Prims.list)=
  let data_from_cache = get_parsing_data_from_cache filename in
  if FStar_Pervasives_Native.uu___is_Some data_from_cache
  then
    let uu___ =
      let uu___1 = FStarC_Option.must data_from_cache in
      deps_from_parsing_data uu___1 original_map filename in
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
    (let uu___1 = FStarC_Parser_Driver.parse_file filename in
     match uu___1 with
     | (ast, uu___2) ->
         let pd = collect_module_or_decls filename (FStar_Pervasives.Inl ast) in
         let pd1 =
           { elts = (FStarC_List.rev pd.elts); no_prelude = (pd.no_prelude) } in
         ((let uu___4 = FStarC_Effect.op_Bang dbg in
           if uu___4
           then
             let uu___5 = FStarC_Class_Show.show showable_parsing_data pd1 in
             FStarC_Format.print2 "Parsing data of %s: %s\n" filename uu___5
           else ());
          (let uu___4 = deps_from_parsing_data pd1 original_map filename in
           match uu___4 with
           | (deps1, has_inline_for_extraction, mo_roots) ->
               ((let uu___6 = FStarC_Effect.op_Bang dbg in
                 if uu___6
                 then
                   let uu___7 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_list showable_dependence)
                       deps1 in
                   FStarC_Format.print2 "Deps for %s: %s\n" filename uu___7
                 else ());
                (pd1, deps1, has_inline_for_extraction, mo_roots)))))
let collect_one_cache :
  (dependence Prims.list * dependence Prims.list * Prims.bool) FStarC_SMap.t
    FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let set_collect_one_cache
  (cache :
    (dependence Prims.list * dependence Prims.list * Prims.bool)
      FStarC_SMap.t)
  : unit= FStarC_Effect.op_Colon_Equals collect_one_cache cache
let dep_graph_copy (dep_graph : dependence_graph) : dependence_graph=
  let uu___ = dep_graph in
  match uu___ with | Deps g -> let uu___1 = FStarC_SMap.copy g in Deps uu___1
let widen_deps (friends1 : module_name Prims.list)
  (dep_graph : dependence_graph) (file_system_map : files_for_module_name)
  (widened : Prims.bool) : (Prims.bool * dependence_graph)=
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
              (fun filename dep_node1 uu___3 ->
                 let uu___4 =
                   let uu___5 = widen_one dep_node1.edges in
                   { edges = uu___5; color = White } in
                 FStarC_SMap.add dg' filename uu___4) ();
            (let uu___3 = FStarC_Effect.op_Bang widened1 in
             (uu___3, (Deps dg')))))
let topological_dependences_of' (file_system_map : files_for_module_name)
  (dep_graph : dependence_graph)
  (interfaces_needing_inlining : Prims.string Prims.list)
  (root_files : file_name Prims.list) (widened : Prims.bool) :
  (file_name Prims.list * Prims.bool)=
  let rec all_friend_deps_1 dep_graph1 cycle uu___ filename =
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
                     (FStarC_Class_Show.show_list showable_dependence)
                     dep_node1.edges in
                 FStarC_Format.print2 "Visiting %s: direct deps are %s\n"
                   filename uu___3
               else ());
              deps_add_dep dep_graph1 filename
                { edges = (dep_node1.edges); color = Gray };
              (let uu___3 =
                 let uu___4 =
                   dependences_of file_system_map dep_graph1 root_files
                     filename in
                 all_friend_deps dep_graph1 cycle (all_friends, all_files)
                   uu___4 in
               match uu___3 with
               | (all_friends1, all_files1) ->
                   (deps_add_dep dep_graph1 filename
                      { edges = (dep_node1.edges); color = Black };
                    (let uu___6 = FStarC_Effect.op_Bang dbg in
                     if uu___6
                     then FStarC_Format.print1 "Adding %s\n" filename
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
  and all_friend_deps dep_graph1 cycle all_friends filenames =
    FStarC_List.fold_left
      (fun all_friends1 k ->
         all_friend_deps_1 dep_graph1 (k :: cycle) all_friends1 k)
      all_friends filenames in
  let uu___ = all_friend_deps dep_graph [] ([], []) root_files in
  match uu___ with
  | (friends1, all_files_0) ->
      ((let uu___2 = FStarC_Effect.op_Bang dbg in
        if uu___2
        then
          let uu___3 =
            let uu___4 =
              remove_dups_fast FStarC_Class_Ord.ord_string friends1 in
            FStarC_String.concat ", " uu___4 in
          FStarC_Format.print3
            "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n"
            (FStarC_String.concat ", " all_files_0) uu___3
            (FStarC_String.concat ", " interfaces_needing_inlining)
        else ());
       (let uu___2 = fly_deps_enabled () in
        if uu___2
        then (all_files_0, false)
        else
          (match friends1 with
           | [] -> (all_files_0, false)
           | uu___4 ->
               let uu___5 =
                 widen_deps friends1 dep_graph file_system_map widened in
               (match uu___5 with
                | (widened1, dep_graph1) ->
                    let uu___6 =
                      (let uu___8 = FStarC_Effect.op_Bang dbg in
                       if uu___8
                       then
                         FStarC_Format.print_string
                           "==============Phase2==================\n"
                       else ());
                      all_friend_deps dep_graph1 [] ([], []) root_files in
                    (match uu___6 with
                     | (uu___7, all_files) ->
                         ((let uu___9 = FStarC_Effect.op_Bang dbg in
                           if uu___9
                           then
                             FStarC_Format.print1
                               "Phase2 complete: all_files = %s\n"
                               (FStarC_String.concat ", " all_files)
                           else ());
                          (all_files, widened1)))))))
let phase1 (file_system_map : files_for_module_name)
  (dep_graph : dependence_graph)
  (interfaces_needing_inlining : module_name Prims.list)
  (for_extraction : Prims.bool) : (Prims.bool * dependence_graph)=
  (let uu___1 = FStarC_Effect.op_Bang dbg in
   if uu___1
   then FStarC_Format.print_string "==============Phase1==================\n"
   else ());
  (let widened = false in
   let uu___1 = (FStarC_Options.cmi ()) && for_extraction in
   if uu___1
   then
     widen_deps interfaces_needing_inlining dep_graph file_system_map widened
   else (widened, dep_graph))
let topological_dependences_of (file_system_map : files_for_module_name)
  (dep_graph : dependence_graph)
  (interfaces_needing_inlining : Prims.string Prims.list)
  (root_files : file_name Prims.list) (for_extraction : Prims.bool) :
  (file_name Prims.list * Prims.bool)=
  let uu___ =
    phase1 file_system_map dep_graph interfaces_needing_inlining
      for_extraction in
  match uu___ with
  | (widened, dep_graph1) ->
      topological_dependences_of' file_system_map dep_graph1
        interfaces_needing_inlining root_files widened
let all_files_in_include_paths (uu___ : unit) : Prims.string Prims.list=
  let paths = FStarC_Find.full_include_path () in
  FStarC_List.collect
    (fun path ->
       let files = safe_readdir_for_include path in
       let files1 =
         FStarC_List.filter
           (fun f ->
              let uu___1 = all_file_suffixes () in
              FStarC_List.existsb (fun ext -> FStarC_Util.ends_with f ext)
                uu___1) files in
       FStarC_List.map (fun file -> FStarC_Filepath.join_paths path file)
         files1) paths
let build_dep_graph_for_files (files : Prims.string Prims.list)
  (file_system_map : files_for_module_name) (dep_graph : dependence_graph)
  (parse_results : parsing_data FStarC_SMap.t)
  (get_parsing_data_from_cache :
    Prims.string -> parsing_data FStar_Pervasives_Native.option)
  : Prims.string Prims.list=
  let interfaces_needing_inlining = FStarC_Effect.mk_ref [] in
  let add_interface_for_inlining l =
    let l1 = lowercase_module_name l in
    let uu___ =
      let uu___1 = FStarC_Effect.op_Bang interfaces_needing_inlining in l1 ::
        uu___1 in
    FStarC_Effect.op_Colon_Equals interfaces_needing_inlining uu___ in
  let rec discover_one file_name1 =
    let uu___ =
      let uu___1 = deps_try_find dep_graph file_name1 in
      uu___1 = FStar_Pervasives_Native.None in
    if uu___
    then
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang collect_one_cache in
          FStarC_SMap.try_find uu___3 file_name1 in
        match uu___2 with
        | FStar_Pervasives_Native.Some cached ->
            (debug_print
               (fun uu___4 ->
                  FStarC_Format.print1 "Using cached parsing data for %s\n"
                    file_name1);
             (empty_parsing_data, cached))
        | FStar_Pervasives_Native.None ->
            let uu___3 =
              collect_one file_system_map file_name1
                get_parsing_data_from_cache in
            (match uu___3 with
             | (parsing_data1, deps1, needs_interface_inlining,
                additional_roots) ->
                 (parsing_data1,
                   (deps1, additional_roots, needs_interface_inlining))) in
      match uu___1 with
      | (parsing_data1, (deps1, mo_roots, needs_interface_inlining)) ->
          (debug_print
             (fun uu___3 ->
                let uu___4 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list showable_dependence) deps1 in
                let uu___5 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list showable_dependence)
                    mo_roots in
                FStarC_Format.print3
                  "collect_one (%s) : deps=%s; mo_roots=%s\n" file_name1
                  uu___4 uu___5);
           if needs_interface_inlining
           then add_interface_for_inlining file_name1
           else ();
           FStarC_SMap.add parse_results file_name1 parsing_data1;
           (let deps2 =
              let uu___5 = maybe_use_interface file_system_map file_name1 in
              FStarC_List.op_At deps1 uu___5 in
            let dep_node1 =
              let uu___5 = FStarC_List.unique deps2 in
              { edges = uu___5; color = White } in
            deps_add_dep dep_graph file_name1 dep_node1;
            (let uu___6 =
               FStarC_List.map (file_of_dep file_system_map files)
                 (FStarC_List.op_At deps2 mo_roots) in
             FStarC_List.iter discover_one uu___6)))
    else () in
  profile (fun uu___1 -> FStarC_List.iter discover_one files)
    "FStarC.Parser.Dep.discover";
  FStarC_Effect.op_Bang interfaces_needing_inlining
let collect_deps_of_decl (deps1 : deps) (filename : Prims.string)
  (ds : FStarC_Parser_AST.decl Prims.list)
  (scope_pds : parsing_data_elt Prims.list)
  (get_parsing_data_from_cache :
    Prims.string -> parsing_data FStar_Pervasives_Native.option)
  : Prims.string Prims.list=
  let roots =
    match ds with
    | { FStarC_Parser_AST.d = FStarC_Parser_AST.TopLevelModule l;
        FStarC_Parser_AST.drange = uu___; FStarC_Parser_AST.quals = uu___1;
        FStarC_Parser_AST.attrs = attrs;
        FStarC_Parser_AST.interleaved = uu___2;_}::uu___3 ->
        ((let uu___5 = FStarC_Effect.op_Bang dbg in
          if uu___5
          then
            let uu___6 =
              FStarC_Class_Show.show FStarC_Ident.showable_lident l in
            let uu___7 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_list FStarC_Parser_AST.showable_term)
                attrs in
            FStarC_Format.print2 "Top-level module %s with attrs=%s\n" uu___6
              uu___7
          else ());
         (let no_prelude =
            (FStarC_Options.no_prelude ()) ||
              (FStarC_List.existsb
                 (fun uu___5 ->
                    match uu___5.FStarC_Parser_AST.tm with
                    | FStarC_Parser_AST.Const (FStarC_Const.Const_string
                        ("no_prelude", uu___6)) -> true
                    | uu___6 -> false) attrs) in
          FStar_Pervasives.Inl
            (FStarC_Parser_AST.Module
               {
                 FStarC_Parser_AST.no_prelude = no_prelude;
                 FStarC_Parser_AST.mname = l;
                 FStarC_Parser_AST.decls = ds
               })))
    | uu___ -> FStar_Pervasives.Inr ds in
  (let uu___1 =
     let uu___2 = FStarC_SMap.keys deps1.file_system_map in
     Prims.uu___is_Nil uu___2 in
   if uu___1
   then build_map deps1.file_system_map deps1.valid_namespaces [filename]
   else ());
  (let pd = collect_module_or_decls filename roots in
   debug_print
     (fun uu___2 ->
        let uu___3 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list showable_parsing_data_elt) pd.elts in
        let uu___4 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list showable_parsing_data_elt) scope_pds in
        FStarC_Format.print2 "Got pds=%s and scope_pds=%s\n" uu___3 uu___4);
   (let pd1 =
      {
        elts =
          (FStarC_List.op_At (FStarC_List.rev scope_pds)
             (FStarC_List.rev pd.elts));
        no_prelude = (pd.no_prelude)
      } in
    let uu___2 = deps_from_parsing_data pd1 deps1.file_system_map filename in
    match uu___2 with
    | (direct_deps, _has_inline_for_extraction, _additional_roots) ->
        (debug_print
           (fun uu___4 ->
              let uu___5 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list
                     FStarC_Parser_AST.showable_decl) ds in
              let uu___6 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list showable_dependence)
                  direct_deps in
              let uu___7 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list showable_dependence)
                  _additional_roots in
              FStarC_Format.print3 "direct deps of %s is %s, mo_roots=%s\n"
                uu___5 uu___6 uu___7);
         (let files =
            FStarC_List.map (file_of_dep deps1.file_system_map [])
              direct_deps in
          let inline_ifaces =
            build_dep_graph_for_files files deps1.file_system_map
              deps1.dep_graph deps1.parse_results get_parsing_data_from_cache in
          let uu___4 =
            topological_dependences_of deps1.file_system_map deps1.dep_graph
              inline_ifaces files false in
          match uu___4 with
          | (filenames, uu___5) ->
              ((let uu___7 =
                  let uu___8 = FStarC_Effect.op_Bang deps1.all_files in
                  let uu___9 =
                    Obj.magic
                      (FStarC_Class_Setlike.from_list ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) filenames) in
                  Obj.magic
                    (FStarC_Class_Setlike.union ()
                       (Obj.magic
                          (FStarC_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) (Obj.magic uu___8)
                       (Obj.magic uu___9)) in
                FStarC_Effect.op_Colon_Equals deps1.all_files uu___7);
               filenames)))))
let collect (all_cmd_line_files : file_name Prims.list)
  (get_parsing_data_from_cache :
    Prims.string -> parsing_data FStar_Pervasives_Native.option)
  : (Prims.string Prims.list * deps)=
  FStarC_Stats.record "Parser.Dep.collect"
    (fun uu___ ->
       let all_cmd_line_files1 =
         match all_cmd_line_files with
         | [] -> all_files_in_include_paths ()
         | uu___1 -> all_cmd_line_files in
       let all_cmd_line_files2 =
         FStarC_List.map
           (fun fn ->
              let uu___1 =
                let uu___2 = FStarC_Parser_ParseIt.read_vfs_entry fn in
                FStar_Pervasives_Native.uu___is_Some uu___2 in
              if uu___1
              then fn
              else
                (let uu___3 = FStarC_Find.find_file fn in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     let uu___4 =
                       FStarC_Format.fmt1 "File %s could not be found" fn in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_ModuleOrFileNotFound ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___4)
                 | FStar_Pervasives_Native.Some fn1 -> fn1))
           all_cmd_line_files1 in
       let dep_graph = deps_empty () in
       let parse_results = FStarC_SMap.create (Prims.of_int (40)) in
       let file_system_map = FStarC_SMap.create (Prims.of_int (41)) in
       let valid_namespaces = FStarC_SMap.create (Prims.of_int (41)) in
       build_map file_system_map valid_namespaces all_cmd_line_files2;
       (let inlining_ifaces =
          build_dep_graph_for_files all_cmd_line_files2 file_system_map
            dep_graph parse_results get_parsing_data_from_cache in
        debug_print
          (fun uu___3 ->
             print_graph FStarC_Util.stdout "stdout" dep_graph
               file_system_map all_cmd_line_files2);
        (let cycle_detected dep_graph1 cycle filename =
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
            (let uu___6 =
               let uu___7 =
                 let uu___8 =
                   FStarC_Format.fmt1 "Recursive dependency on module %s."
                     filename in
                 FStarC_Errors_Msg.text uu___8 in
               let uu___8 =
                 let uu___9 =
                   FStarC_Errors_Msg.text
                     "A full dependency graph was written to dep.graph." in
                 [uu___9] in
               uu___7 :: uu___8 in
             FStarC_Errors.raise_error0
               FStarC_Errors_Codes.Fatal_CyclicDependence ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___6))) in
         let full_cycle_detection all_command_line_files file_system_map1 =
           let dep_graph1 = dep_graph_copy dep_graph in
           let mo_files = FStarC_Effect.mk_ref [] in
           let rec aux cycle filename =
             let node =
               let uu___3 = deps_try_find dep_graph1 filename in
               match uu___3 with
               | FStar_Pervasives_Native.Some node1 -> node1
               | FStar_Pervasives_Native.None ->
                   let uu___4 =
                     FStarC_Format.fmt1
                       "Impossible: Failed to find dependencies of %s"
                       filename in
                   failwith uu___4 in
             let direct_deps =
               FStarC_List.collect
                 (fun x ->
                    match x with
                    | UseInterface f ->
                        let uu___3 =
                          implementation_of_internal file_system_map1 f in
                        (match uu___3 with
                         | FStar_Pervasives_Native.None -> [x]
                         | FStar_Pervasives_Native.Some fn when fn = filename
                             -> [x]
                         | uu___4 ->
                             let uu___5 = peek_past_interfaces () in
                             if uu___5 then [x; UseImplementation f] else [x])
                    | PreferInterface f ->
                        let uu___3 =
                          implementation_of_internal file_system_map1 f in
                        (match uu___3 with
                         | FStar_Pervasives_Native.None -> [x]
                         | FStar_Pervasives_Native.Some fn when fn = filename
                             -> [x]
                         | uu___4 ->
                             let uu___5 = peek_past_interfaces () in
                             if uu___5 then [x; UseImplementation f] else [x])
                    | uu___3 -> [x]) node.edges in
             match node.color with
             | Gray -> cycle_detected dep_graph1 cycle filename
             | Black -> ()
             | White ->
                 (deps_add_dep dep_graph1 filename
                    { edges = direct_deps; color = Gray };
                  (let uu___5 =
                     dependences_of file_system_map1 dep_graph1
                       all_command_line_files filename in
                   FStarC_List.iter (fun k -> aux (k :: cycle) k) uu___5);
                  deps_add_dep dep_graph1 filename
                    { edges = direct_deps; color = Black };
                  (let uu___6 =
                     (is_interface filename) && (peek_past_interfaces ()) in
                   if uu___6
                   then
                     let uu___7 =
                       let uu___8 = lowercase_module_name filename in
                       implementation_of_internal file_system_map1 uu___8 in
                     FStarC_Option.iter
                       (fun impl ->
                          if
                            Prims.op_Negation
                              (FStarC_List.contains impl
                                 all_command_line_files)
                          then
                            let uu___8 =
                              let uu___9 = FStarC_Effect.op_Bang mo_files in
                              impl :: uu___9 in
                            FStarC_Effect.op_Colon_Equals mo_files uu___8
                          else ()) uu___7
                   else ())) in
           FStarC_List.iter (aux []) all_command_line_files;
           (let uu___4 = FStarC_Effect.op_Bang mo_files in
            FStarC_List.iter (aux []) uu___4) in
         full_cycle_detection all_cmd_line_files2 file_system_map;
         FStarC_List.iter
           (fun f ->
              let m = lowercase_module_name f in
              FStarC_Options.add_verify_module m) all_cmd_line_files2;
         (let uu___5 =
            profile
              (fun uu___6 ->
                 let uu___7 =
                   let uu___8 = FStarC_Options.codegen () in
                   uu___8 <> FStar_Pervasives_Native.None in
                 topological_dependences_of file_system_map dep_graph
                   inlining_ifaces all_cmd_line_files2 uu___7)
              "FStarC.Parser.Dep.topological_dependences_of" in
          match uu___5 with
          | (all_files, uu___6) ->
              ((let uu___8 = FStarC_Effect.op_Bang dbg in
                if uu___8
                then
                  FStarC_Format.print1 "Interfaces needing inlining: %s\n"
                    (FStarC_String.concat ", " inlining_ifaces)
                else ());
               (let uu___8 =
                  let uu___9 =
                    Obj.magic
                      (FStarC_Class_Setlike.from_list ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) all_files) in
                  mk_deps dep_graph file_system_map valid_namespaces
                    all_cmd_line_files2 uu___9 inlining_ifaces parse_results in
                (all_files, uu___8)))))))
let parsing_data_of_modul (deps1 : deps) (filename : Prims.string)
  (modul_opt : FStarC_Parser_AST.modul FStar_Pervasives_Native.option) :
  (parsing_data * Prims.string Prims.list)=
  let modul =
    match modul_opt with
    | FStar_Pervasives_Native.None ->
        let uu___ = FStarC_Parser_Driver.parse_file filename in
        (match uu___ with | (ast, uu___1) -> ast)
    | FStar_Pervasives_Native.Some m -> m in
  let pd = collect_module_or_decls filename (FStar_Pervasives.Inl modul) in
  let pd1 =
    { elts = (FStarC_List.rev pd.elts); no_prelude = (pd.no_prelude) } in
  let uu___ = deps_from_parsing_data pd1 deps1.file_system_map filename in
  match uu___ with
  | (direct_deps, uu___1, uu___2) ->
      let uu___3 =
        files_of_dependences filename deps1.file_system_map
          deps1.cmd_line_files direct_deps in
      (pd1, uu___3)
let deps_of : deps -> Prims.string -> Prims.string Prims.list=
  let cache = FStarC_SMap.create (Prims.of_int (40)) in
  fun deps1 f ->
    let uu___ = FStarC_SMap.try_find cache f in
    match uu___ with
    | FStar_Pervasives_Native.Some deps2 -> deps2
    | FStar_Pervasives_Native.None ->
        let res =
          let uu___1 = fly_deps_enabled () in
          if uu___1
          then
            let on_cli f1 =
              let bf = FStarC_Filepath.basename f1 in
              FStarC_List.existsb
                (fun cli ->
                   let uu___2 = FStarC_Filepath.basename cli in uu___2 = bf)
                deps1.cmd_line_files in
            let uu___2 =
              (on_cli f) ||
                ((is_interface f) &&
                   (let uu___3 = implementation_of_file f in on_cli uu___3)) in
            (if uu___2
             then
               let uu___3 =
                 parsing_data_of_modul deps1 f FStar_Pervasives_Native.None in
               FStar_Pervasives_Native.snd uu___3
             else
               dependences_of deps1.file_system_map deps1.dep_graph
                 deps1.cmd_line_files f)
          else
            dependences_of deps1.file_system_map deps1.dep_graph
              deps1.cmd_line_files f in
        (FStarC_SMap.add cache f res; res)
let deps_of_modul (deps1 : deps) (m : module_name) : module_name Prims.list=
  let aux fopt =
    let uu___ =
      FStarC_Option.map
        (fun f ->
           let uu___1 = deps_of deps1 f in
           FStarC_List.map module_name_of_file uu___1) fopt in
    FStarC_Option.dflt [] uu___ in
  let uu___ =
    let uu___1 =
      FStarC_SMap.try_find deps1.file_system_map (FStarC_String.lowercase m) in
    FStarC_Option.map
      (fun uu___2 ->
         match uu___2 with
         | (intf_opt, impl_opt) ->
             let uu___3 =
               let uu___4 = aux intf_opt in
               let uu___5 = aux impl_opt in FStarC_List.op_At uu___4 uu___5 in
             remove_dups_fast FStarC_Class_Ord.ord_string uu___3) uu___1 in
  FStarC_Option.dflt [] uu___
let parsing_data_of (deps1 : deps) (fn : Prims.string) : parsing_data=
  let uu___ = FStarC_SMap.try_find deps1.parse_results fn in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 = FStarC_Format.fmt1 "Parsing data not found for %s" fn in
      failwith uu___1
  | FStar_Pervasives_Native.Some pd -> pd
let populate_parsing_data (fn : Prims.string)
  (ast_modul : FStarC_Parser_AST.modul) (deps1 : deps) : unit=
  let uu___ = FStarC_SMap.try_find deps1.parse_results fn in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let pd = collect_module_or_decls fn (FStar_Pervasives.Inl ast_modul) in
      FStarC_SMap.add deps1.parse_results fn pd
  | FStar_Pervasives_Native.Some uu___1 -> ()
let print_digest (dig : (Prims.string * Prims.string) Prims.list) :
  Prims.string=
  FStarC_Class_Show.show
    (FStarC_Class_Show.show_list
       (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_string
          FStarC_Class_Show.showable_string)) dig
let print_make (outc : FStarC_Util.out_channel) (deps1 : deps) : unit=
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
       FStarC_Format.print2 "%s: %s\n\n" f (FStarC_String.concat " " files1))
    keys
let print_raw (outc : FStarC_Util.out_channel) (deps1 : deps) : unit=
  let uu___ = deps1.dep_graph in
  match uu___ with
  | Deps deps2 ->
      let uu___1 =
        let uu___2 =
          FStarC_SMap.fold deps2
            (fun k dep_node1 out ->
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStarC_List.map dep_to_string dep_node1.edges in
                   FStarC_String.concat ";\n\t" uu___5 in
                 FStarC_Format.fmt2 "%s -> [\n\t%s\n] " k uu___4 in
               uu___3 :: out) [] in
        FStarC_String.concat ";;\n" uu___2 in
      FStarC_Util.fprint outc "%s\n" [uu___1]
let print_full (outc : FStarC_Util.out_channel) (deps1 : deps) : unit=
  let pre_tag = FStarC_Options_Ext.get "dep_pretag" in
  let sort_output_files orig_output_file_map =
    let order = FStarC_Effect.mk_ref [] in
    let remaining_output_files = FStarC_SMap.copy orig_output_file_map in
    let visited_other_modules = FStarC_SMap.create (Prims.of_int (41)) in
    let should_visit lc_module_name =
      (let uu___ = FStarC_SMap.try_find remaining_output_files lc_module_name in
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
                         "Impossible: module %s: %s not found" lc_module_name
                         file_name1 in
                     failwith uu___2
                 | FStar_Pervasives_Native.Some
                     { edges = immediate_deps; color = uu___2;_} ->
                     let immediate_deps1 =
                       FStarC_List.map
                         (fun x ->
                            FStarC_String.lowercase (module_name_of_dep x))
                         immediate_deps in
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
    FStarC_Util.replace_chars (FStarC_Util.replace_chars s 92 "/") 32 "\\ " in
  let print_entry target all_deps =
    pr target;
    pr ":";
    FStarC_List.iter (fun f -> pr " \\\n\t"; pr (norm_path f)) all_deps;
    pr "\n\n" in
  let print_all tag files =
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
  let output_file ext fst_file =
    let basename =
      let uu___ =
        let uu___1 = FStarC_Filepath.basename fst_file in
        check_and_strip_suffix uu___1 in
      FStarC_Option.must uu___ in
    let basename1 = no_fstar_stubs_file basename in
    let ml_base_name = FStarC_Util.replace_chars basename1 46 "_" in
    FStarC_Find.prepend_output_dir (Prims.strcat ml_base_name ext) in
  let output_fs_file f = let uu___ = output_file ".fs" f in norm_path uu___ in
  let output_ml_file f = let uu___ = output_file ".ml" f in norm_path uu___ in
  let output_krml_file f =
    let uu___ = output_file ".krml" f in norm_path uu___ in
  let output_cmx_file f = let uu___ = output_file ".cmx" f in norm_path uu___ in
  let cache_file f = let uu___ = cache_file_name f in norm_path uu___ in
  let uu___ =
    phase1 deps1.file_system_map deps1.dep_graph
      deps1.interfaces_with_inlining true in
  match uu___ with
  | (widened, dep_graph) ->
      let all_checked_files =
        FStarC_List.fold_left
          (fun all_checked_files1 file_name1 ->
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
                                 (dep_subsumed_by iface_dep) dep_node1.edges in
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
                             (file_of_dep_aux true deps1.file_system_map
                                deps1.cmd_line_files) iface_deps2 in
                         remove_dups_fast FStarC_Class_Ord.ord_string
                           (FStarC_List.op_At files iface_files) in
                   let files2 =
                     if FStar_Pervasives_Native.uu___is_Some iface_fn
                     then
                       let iface_fn1 = FStarC_Option.must iface_fn in
                       let uu___3 =
                         FStarC_List.filter (fun f -> f <> iface_fn1) files1 in
                       let uu___4 = cache_file_name iface_fn1 in uu___4 ::
                         uu___3
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
                       (print_entry cache_file_name1 (file_name1 :: files2);
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
                            topological_dependences_of' deps1.file_system_map
                              uu___6 deps1.interfaces_with_inlining
                              [file_name1] widened)
                         "FStarC.Parser.Dep.topological_dependences_of_2"
                     else
                       (let maybe_widen_deps f_deps =
                          FStarC_List.map
                            (fun dep ->
                               file_of_dep_aux false deps1.file_system_map
                                 deps1.cmd_line_files dep) f_deps in
                        let fst_files = maybe_widen_deps dep_node1.edges in
                        let fst_files_from_iface =
                          match iface_deps1 with
                          | FStar_Pervasives_Native.None -> []
                          | FStar_Pervasives_Native.Some iface_deps2 ->
                              maybe_widen_deps iface_deps2 in
                        let uu___6 =
                          remove_dups_fast FStarC_Class_Ord.ord_string
                            (FStarC_List.op_At fst_files fst_files_from_iface) in
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
                                let mname = lowercase_module_name file_name1 in
                                ((let uu___9 = output_ml_file file_name1 in
                                  print_entry uu___9 (cache_file_name1 ::
                                    all_checked_fst_dep_files));
                                 (let uu___10 =
                                    FStarC_Options.should_extract mname
                                      FStarC_Options.FSharp in
                                  if uu___10
                                  then
                                    let uu___11 = output_fs_file file_name1 in
                                    print_entry uu___11 (cache_file_name1 ::
                                      all_checked_fst_dep_files)
                                  else ());
                                 (let uu___10 = output_krml_file file_name1 in
                                  print_entry uu___10 (cache_file_name1 ::
                                    all_checked_fst_dep_files)))
                              else
                                (let mname = lowercase_module_name file_name1 in
                                 (let uu___10 = output_ml_file file_name1 in
                                  print_entry uu___10 [cache_file_name1]);
                                 (let uu___11 =
                                    FStarC_Options.should_extract mname
                                      FStarC_Options.FSharp in
                                  if uu___11
                                  then
                                    let uu___12 = output_fs_file file_name1 in
                                    print_entry uu___12 [cache_file_name1]
                                  else ());
                                 (let uu___11 = output_krml_file file_name1 in
                                  print_entry uu___11 [cache_file_name1])));
                             (let cmx_files =
                                let extracted_fst_files =
                                  FStarC_List.filter
                                    (fun df ->
                                       (let uu___7 = lowercase_module_name df in
                                        let uu___8 =
                                          lowercase_module_name file_name1 in
                                        uu___7 <> uu___8) &&
                                         (let uu___7 =
                                            lowercase_module_name df in
                                          FStarC_Options.should_extract
                                            uu___7 FStarC_Options.OCaml))
                                    all_fst_files_dep in
                                FStarC_List.map output_cmx_file
                                  extracted_fst_files in
                              let uu___7 =
                                let uu___8 = lowercase_module_name file_name1 in
                                FStarC_Options.should_extract uu___8
                                  FStarC_Options.OCaml in
                              if uu___7
                              then
                                let uu___8 = output_cmx_file file_name1 in
                                let uu___9 =
                                  let uu___10 = output_ml_file file_name1 in
                                  uu___10 :: cmx_files in
                                print_entry uu___8 uu___9
                              else ()))
                          else
                            (let uu___7 =
                               (let uu___8 =
                                  let uu___9 =
                                    lowercase_module_name file_name1 in
                                  has_implementation deps1.file_system_map
                                    uu___9 in
                                Prims.op_Negation uu___8) &&
                                 (is_interface file_name1) in
                             if uu___7
                             then
                               let uu___8 =
                                 (FStarC_Options.cmi ()) &&
                                   (widened1 || true) in
                               (if uu___8
                                then
                                  let uu___9 = output_krml_file file_name1 in
                                  print_entry uu___9 (cache_file_name1 ::
                                    all_checked_fst_dep_files)
                                else
                                  (let uu___10 = output_krml_file file_name1 in
                                   print_entry uu___10 [cache_file_name1]))
                             else ()));
                         all_checked_files2)) in
             profile process_one_key "FStarC.Parser.Dep.process_one_key") []
          keys in
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
                  "Interface %s is admitted without an implementation" uu___5 in
              FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                uu___3 FStarC_Errors_Codes.Warning_WarnOnUse ()
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
let do_print (outc : FStarC_Util.out_channel) (fn : Prims.string)
  (deps1 : deps) : unit=
  let pref uu___ =
    (let uu___2 =
       let uu___3 = FStarC_Effect.op_Bang FStarC_Options._version in [uu___3] in
     FStarC_Util.fprint outc "# This .depend was generated by F* %s\n" uu___2);
    (let uu___3 =
       let uu___4 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_string
           FStarC_Util.exec_name in
       [uu___4] in
     FStarC_Util.fprint outc "# Executable: %s\n" uu___3);
    (let uu___4 =
       let uu___5 = FStarC_Effect.op_Bang FStarC_Options._commit in [uu___5] in
     FStarC_Util.fprint outc "# Hash: %s\n" uu___4);
    (let uu___5 =
       let uu___6 =
         let uu___7 =
           let uu___8 = FStarC_Util.getcwd () in
           FStarC_Filepath.normalize_file_path uu___8 in
         FStarC_Class_Show.show FStarC_Class_Show.showable_string uu___7 in
       [uu___6] in
     FStarC_Util.fprint outc "# Running in directory %s\n" uu___5);
    (let uu___6 =
       let uu___7 =
         let uu___8 = FStarC_Util.get_cmd_args () in
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
           uu___8 in
       [uu___7] in
     FStarC_Util.fprint outc "# Command line arguments: \"%s\"\n" uu___6);
    FStarC_Util.fprint outc "\n" [] in
  let uu___ = FStarC_Options.dep () in
  match uu___ with
  | FStar_Pervasives_Native.Some "make" -> (pref (); print_make outc deps1)
  | FStar_Pervasives_Native.Some "full" ->
      (pref ();
       profile (fun uu___2 -> print_full outc deps1)
         "FStarC.Parser.Deps.print_full_deps")
  | FStar_Pervasives_Native.Some "graph" ->
      print_graph outc fn deps1.dep_graph deps1.file_system_map
        deps1.cmd_line_files
  | FStar_Pervasives_Native.Some "raw" -> print_raw outc deps1
  | FStar_Pervasives_Native.Some uu___1 ->
      FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_UnknownToolForDep
        () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic "unknown tool for --dep\n")
  | FStar_Pervasives_Native.None -> ()
let do_print_stdout (deps1 : deps) : unit=
  do_print FStarC_Util.stdout "<stdout>" deps1
let do_print_file (deps1 : deps) (fn : Prims.string) : unit=
  with_file_outchannel fn (fun outc -> do_print outc fn deps1)
let print (deps1 : deps) : unit=
  let uu___ = FStarC_Options.output_deps_to () in
  match uu___ with
  | FStar_Pervasives_Native.Some s -> do_print_file deps1 s
  | FStar_Pervasives_Native.None when
      let uu___1 = FStarC_Options.dep () in
      uu___1 = (FStar_Pervasives_Native.Some "graph") ->
      do_print_file deps1 "dep.graph"
  | FStar_Pervasives_Native.None -> do_print_stdout deps1
let module_has_interface (deps1 : deps) (module_name1 : FStarC_Ident.lident)
  : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid module_name1 in
    FStarC_String.lowercase uu___1 in
  has_interface deps1.file_system_map uu___
let deps_has_implementation (deps1 : deps)
  (module_name1 : FStarC_Ident.lident) : Prims.bool=
  let m =
    let uu___ = FStarC_Ident.string_of_lid module_name1 in
    FStarC_String.lowercase uu___ in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang deps1.all_files in
    FStarC_Class_Setlike.elems ()
      (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
      (Obj.magic uu___1) in
  FStarC_Util.for_some
    (fun f ->
       (is_implementation f) &&
         (let uu___1 =
            let uu___2 = module_name_of_file f in
            FStarC_String.lowercase uu___2 in
          uu___1 = m)) uu___
let all_files (deps1 : deps) : Prims.string Prims.list=
  let uu___ = FStarC_Effect.op_Bang deps1.all_files in
  FStarC_Class_Setlike.elems ()
    (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
    (Obj.magic uu___)
