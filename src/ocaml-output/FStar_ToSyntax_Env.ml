open Prims
type local_binding =
  (FStar_Ident.ident,FStar_Syntax_Syntax.bv,Prims.bool)
    FStar_Pervasives_Native.tuple3
type rec_binding =
  (FStar_Ident.ident,FStar_Ident.lid,FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3
type module_abbrev =
  (FStar_Ident.ident,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
type open_kind =
  | Open_module
  | Open_namespace
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____20 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____24 -> false
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}
type scope_mod =
  | Local_binding of local_binding
  | Rec_binding of rec_binding
  | Module_abbrev of module_abbrev
  | Open_module_or_namespace of open_module_or_namespace
  | Top_level_def of FStar_Ident.ident
  | Record_or_dc of record_or_dc
let uu___is_Local_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____123 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____135 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____147 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____159 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____171 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____183 -> false
let __proj__Record_or_dc__item___0: scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____196 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____200 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option;
  modules:
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap:
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  syntax_only: Prims.bool;}
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____465 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____493 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___174_519 = env in
      {
        curmodule = (uu___174_519.curmodule);
        curmonad = (uu___174_519.curmonad);
        modules = (uu___174_519.modules);
        scope_mods = (uu___174_519.scope_mods);
        exported_ids = (uu___174_519.exported_ids);
        trans_exported_ids = (uu___174_519.trans_exported_ids);
        includes = (uu___174_519.includes);
        sigaccum = (uu___174_519.sigaccum);
        sigmap = (uu___174_519.sigmap);
        iface = b;
        admitted_iface = (uu___174_519.admitted_iface);
        expect_typ = (uu___174_519.expect_typ);
        docs = (uu___174_519.docs);
        remaining_iface_decls = (uu___174_519.remaining_iface_decls);
        syntax_only = (uu___174_519.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_529 = e in
      {
        curmodule = (uu___175_529.curmodule);
        curmonad = (uu___175_529.curmonad);
        modules = (uu___175_529.modules);
        scope_mods = (uu___175_529.scope_mods);
        exported_ids = (uu___175_529.exported_ids);
        trans_exported_ids = (uu___175_529.trans_exported_ids);
        includes = (uu___175_529.includes);
        sigaccum = (uu___175_529.sigaccum);
        sigmap = (uu___175_529.sigmap);
        iface = (uu___175_529.iface);
        admitted_iface = b;
        expect_typ = (uu___175_529.expect_typ);
        docs = (uu___175_529.docs);
        remaining_iface_decls = (uu___175_529.remaining_iface_decls);
        syntax_only = (uu___175_529.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___176_539 = e in
      {
        curmodule = (uu___176_539.curmodule);
        curmonad = (uu___176_539.curmonad);
        modules = (uu___176_539.modules);
        scope_mods = (uu___176_539.scope_mods);
        exported_ids = (uu___176_539.exported_ids);
        trans_exported_ids = (uu___176_539.trans_exported_ids);
        includes = (uu___176_539.includes);
        sigaccum = (uu___176_539.sigaccum);
        sigmap = (uu___176_539.sigmap);
        iface = (uu___176_539.iface);
        admitted_iface = (uu___176_539.admitted_iface);
        expect_typ = b;
        docs = (uu___176_539.docs);
        remaining_iface_decls = (uu___176_539.remaining_iface_decls);
        syntax_only = (uu___176_539.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____554 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____554 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____560 =
            let uu____561 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____561 in
          FStar_All.pipe_right uu____560 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___177_584 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___177_584.curmonad);
        modules = (uu___177_584.modules);
        scope_mods = (uu___177_584.scope_mods);
        exported_ids = (uu___177_584.exported_ids);
        trans_exported_ids = (uu___177_584.trans_exported_ids);
        includes = (uu___177_584.includes);
        sigaccum = (uu___177_584.sigaccum);
        sigmap = (uu___177_584.sigmap);
        iface = (uu___177_584.iface);
        admitted_iface = (uu___177_584.admitted_iface);
        expect_typ = (uu___177_584.expect_typ);
        docs = (uu___177_584.docs);
        remaining_iface_decls = (uu___177_584.remaining_iface_decls);
        syntax_only = (uu___177_584.syntax_only)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let iface_decls:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____599 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____630  ->
                match uu____630 with
                | (m,uu____638) -> FStar_Ident.lid_equals l m)) in
      match uu____599 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____655,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____682 =
          FStar_List.partition
            (fun uu____709  ->
               match uu____709 with
               | (m,uu____717) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____682 with
        | (uu____722,rest) ->
            let uu___178_756 = env in
            {
              curmodule = (uu___178_756.curmodule);
              curmonad = (uu___178_756.curmonad);
              modules = (uu___178_756.modules);
              scope_mods = (uu___178_756.scope_mods);
              exported_ids = (uu___178_756.exported_ids);
              trans_exported_ids = (uu___178_756.trans_exported_ids);
              includes = (uu___178_756.includes);
              sigaccum = (uu___178_756.sigaccum);
              sigmap = (uu___178_756.sigmap);
              iface = (uu___178_756.iface);
              admitted_iface = (uu___178_756.admitted_iface);
              expect_typ = (uu___178_756.expect_typ);
              docs = (uu___178_756.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___178_756.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____775 = current_module env in qual uu____775 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____777 =
            let uu____778 = current_module env in qual uu____778 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____777 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___179_788 = env in
      {
        curmodule = (uu___179_788.curmodule);
        curmonad = (uu___179_788.curmonad);
        modules = (uu___179_788.modules);
        scope_mods = (uu___179_788.scope_mods);
        exported_ids = (uu___179_788.exported_ids);
        trans_exported_ids = (uu___179_788.trans_exported_ids);
        includes = (uu___179_788.includes);
        sigaccum = (uu___179_788.sigaccum);
        sigmap = (uu___179_788.sigmap);
        iface = (uu___179_788.iface);
        admitted_iface = (uu___179_788.admitted_iface);
        expect_typ = (uu___179_788.expect_typ);
        docs = (uu___179_788.docs);
        remaining_iface_decls = (uu___179_788.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____797 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____800  ->
    let uu____801 = new_sigmap () in
    let uu____804 = new_sigmap () in
    let uu____807 = new_sigmap () in
    let uu____818 = new_sigmap () in
    let uu____829 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____801;
      trans_exported_ids = uu____804;
      includes = uu____807;
      sigaccum = [];
      sigmap = uu____818;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____829;
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  = fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____858  ->
         match uu____858 with
         | (m,uu____864) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___180_872 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___180_872.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___181_873 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___181_873.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___181_873.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
let unmangleOpName:
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun id  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____954  ->
           match uu____954 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____977 =
                   let uu____978 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____978 dd dq in
                 FStar_Pervasives_Native.Some uu____977
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____1021 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____1050 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____1064 -> false
let option_of_cont k_ignore uu___146_1087 =
  match uu___146_1087 with
  | Cont_ok a -> FStar_Pervasives_Native.Some a
  | Cont_fail  -> FStar_Pervasives_Native.None
  | Cont_ignore  -> k_ignore ()
let find_in_record ns id record cont =
  let typename' =
    FStar_Ident.lid_of_ids
      (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
  if FStar_Ident.lid_equals typename' record.typename
  then
    let fname =
      FStar_Ident.lid_of_ids
        (FStar_List.append (record.typename).FStar_Ident.ns [id]) in
    let find1 =
      FStar_Util.find_map record.fields
        (fun uu____1143  ->
           match uu____1143 with
           | (f,uu____1151) ->
               if id.FStar_Ident.idText = f.FStar_Ident.idText
               then FStar_Pervasives_Native.Some record
               else FStar_Pervasives_Native.None) in
    match find1 with
    | FStar_Pervasives_Native.Some r -> cont r
    | FStar_Pervasives_Native.None  -> Cont_ignore
  else Cont_ignore
let get_exported_id_set:
  env -> Prims.string -> exported_id_set FStar_Pervasives_Native.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env -> Prims.string -> exported_id_set FStar_Pervasives_Native.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___147_1197  ->
    match uu___147_1197 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___148_1253 =
    match uu___148_1253 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____1264 = get_exported_id_set env mname in
          match uu____1264 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some mex ->
              let mexports =
                let uu____1285 = mex eikind in FStar_ST.read uu____1285 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____1294 = FStar_Util.smap_try_find env.includes mname in
          match uu____1294 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____1329 = qual modul id in find_in_module uu____1329
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1333 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___149_1338  ->
    match uu___149_1338 with
    | Exported_id_field  -> true
    | uu____1339 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___150_1441 =
    match uu___150_1441 with
    | (id',uu____1443,uu____1444) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___151_1448 =
    match uu___151_1448 with
    | (id',uu____1450,uu____1451) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1455 = current_module env in FStar_Ident.ids_of_lid uu____1455 in
  let proc uu___152_1461 =
    match uu___152_1461 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,Open_module ) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1469 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1469 id
    | uu____1472 -> Cont_ignore in
  let rec aux uu___153_1480 =
    match uu___153_1480 with
    | a::q ->
        let uu____1489 = proc a in
        option_of_cont (fun uu____1492  -> aux q) uu____1489
    | [] ->
        let uu____1493 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1496  -> FStar_Pervasives_Native.None)
          uu____1493 in
  aux env.scope_mods
let found_local_binding r uu____1520 =
  match uu____1520 with
  | (id',x,mut) -> let uu____1530 = bv_to_name x r in (uu____1530, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1571 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1571 with
  | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
  | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id  ->
      let uu____1607 = unmangleOpName id in
      match uu____1607 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____1633 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1645 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1645) (fun uu____1654  -> Cont_fail)
            (fun uu____1659  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1671  -> fun uu____1672  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1685  -> fun uu____1686  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | FStar_Pervasives_Native.Some uu____1756 ->
        let lid = qualify env id in
        let uu____1758 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1758 with
         | FStar_Pervasives_Native.Some r ->
             let uu____1782 = k_global_def lid r in
             FStar_Pervasives_Native.Some uu____1782
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
  match find_in_monad with
  | FStar_Pervasives_Native.Some v1 -> v1
  | FStar_Pervasives_Native.None  ->
      let lid = let uu____1805 = current_module env in qual uu____1805 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____1815 = current_module env in
           FStar_Ident.lid_equals lid uu____1815)
        ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
let resolve_module_name:
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___154_1846 =
          match uu___154_1846 with
          | [] ->
              let uu____1851 = module_is_defined env lid in
              if uu____1851
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1860 =
                  let uu____1863 = FStar_Ident.path_of_lid ns in
                  let uu____1866 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1863 uu____1866 in
                FStar_Ident.lid_of_path uu____1860
                  (FStar_Ident.range_of_lid lid) in
              let uu____1869 = module_is_defined env new_lid in
              if uu____1869
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____1875 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____1880::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1893 =
          let uu____1894 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1894 in
        if uu____1893
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____1896 =
                let uu____1897 =
                  let uu____1902 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1902, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1897 in
              raise uu____1896))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1910 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1914 = resolve_module_name env modul_orig true in
          (match uu____1914 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____1918 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___155_1927  ->
           match uu___155_1927 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1929 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____2018 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____2018
                   (FStar_Util.map_option
                      (fun uu____2065  ->
                         match uu____2065 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____2096 =
          is_full_path &&
            (let uu____2097 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____2097) in
        if uu____2096
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____2127 = aux ns_rev_prefix ns_last_id in
               (match uu____2127 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____2186 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____2186 with
      | (uu____2195,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____2303::uu____2304 ->
      let uu____2307 =
        let uu____2310 =
          let uu____2311 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____2311 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____2310 true in
      (match uu____2307 with
       | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some modul ->
           let uu____2315 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____2318  -> FStar_Pervasives_Native.None)
             uu____2315)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___156_2336 =
  match uu___156_2336 with
  | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
  | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____2435 = k_global_def lid1 def in cont_of_option k uu____2435 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____2463 = k_local_binding l in
       cont_of_option Cont_fail uu____2463)
    (fun r  ->
       let uu____2467 = k_rec_binding r in
       cont_of_option Cont_fail uu____2467) (fun uu____2470  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____2478,uu____2479,uu____2480,l,uu____2482,uu____2483) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___157_2491  ->
               match uu___157_2491 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____2494,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____2506 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____2512,uu____2513,uu____2514)
        -> FStar_Pervasives_Native.None
    | uu____2515 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____2526 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____2531 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____2531
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2526 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____2543 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____2543 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___161_2573 =
            match uu___161_2573 with
            | (uu____2580,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____2582) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____2585 ->
                     let uu____2602 =
                       let uu____2603 =
                         let uu____2608 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____2608, false) in
                       Term_name uu____2603 in
                     FStar_Pervasives_Native.Some uu____2602
                 | FStar_Syntax_Syntax.Sig_datacon uu____2609 ->
                     let uu____2624 =
                       let uu____2625 =
                         let uu____2630 =
                           let uu____2631 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____2631 in
                         (uu____2630, false) in
                       Term_name uu____2625 in
                     FStar_Pervasives_Native.Some uu____2624
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____2634,lbs),uu____2636,uu____2637) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____2657 =
                       let uu____2658 =
                         let uu____2663 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____2663, false) in
                       Term_name uu____2658 in
                     FStar_Pervasives_Native.Some uu____2657
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____2665,uu____2666) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____2670 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___158_2673  ->
                                  match uu___158_2673 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____2674 -> false))) in
                     if uu____2670
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____2679 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Parser_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___159_2682  ->
                                         match uu___159_2682 with
                                         | FStar_Syntax_Syntax.Projector
                                             uu____2683 -> true
                                         | FStar_Syntax_Syntax.Discriminator
                                             uu____2688 -> true
                                         | uu____2689 -> false)))) in
                         if uu____2679
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____2691 =
                         FStar_Util.find_map quals
                           (fun uu___160_2694  ->
                              match uu___160_2694 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____2698 -> FStar_Pervasives_Native.None) in
                       (match uu____2691 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____2711 ->
                            let uu____2714 =
                              let uu____2715 =
                                let uu____2720 =
                                  let uu____2721 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2721 in
                                (uu____2720, false) in
                              Term_name uu____2715 in
                            FStar_Pervasives_Native.Some uu____2714)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2727 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____2740 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____2759 =
              let uu____2760 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2760 in
            FStar_Pervasives_Native.Some uu____2759 in
          let k_rec_binding uu____2776 =
            match uu____2776 with
            | (id,l,dd) ->
                let uu____2788 =
                  let uu____2789 =
                    let uu____2794 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____2794, false) in
                  Term_name uu____2789 in
                FStar_Pervasives_Native.Some uu____2788 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2800 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2800 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____2818 -> FStar_Pervasives_Native.None)
            | uu____2825 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____2854 = try_lookup_name true exclude_interf env lid in
        match uu____2854 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____2869 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2884 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2884 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____2899 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2920 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2920 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2936;
             FStar_Syntax_Syntax.sigquals = uu____2937;
             FStar_Syntax_Syntax.sigmeta = uu____2938;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2955;
             FStar_Syntax_Syntax.sigquals = uu____2956;
             FStar_Syntax_Syntax.sigmeta = uu____2957;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2973,uu____2974,uu____2975,uu____2976,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2978;
             FStar_Syntax_Syntax.sigquals = uu____2979;
             FStar_Syntax_Syntax.sigmeta = uu____2980;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____3000 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3021 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____3021 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____3031;
             FStar_Syntax_Syntax.sigquals = uu____3032;
             FStar_Syntax_Syntax.sigmeta = uu____3033;_},uu____3034)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____3042;
             FStar_Syntax_Syntax.sigquals = uu____3043;
             FStar_Syntax_Syntax.sigmeta = uu____3044;_},uu____3045)
          -> FStar_Pervasives_Native.Some ne
      | uu____3052 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3065 = try_lookup_effect_name env lid in
      match uu____3065 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____3068 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3077 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____3077 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____3087,uu____3088,uu____3089,uu____3090);
             FStar_Syntax_Syntax.sigrng = uu____3091;
             FStar_Syntax_Syntax.sigquals = uu____3092;
             FStar_Syntax_Syntax.sigmeta = uu____3093;_},uu____3094)
          ->
          let rec aux new_name =
            let uu____3111 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____3111 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____3129) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____3138,uu____3139,uu____3140,cmp,uu____3142) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____3148 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____3149,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____3155 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_3184 =
        match uu___162_3184 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3193,uu____3194,uu____3195);
             FStar_Syntax_Syntax.sigrng = uu____3196;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3198;_},uu____3199)
            -> FStar_Pervasives_Native.Some quals
        | uu____3204 -> FStar_Pervasives_Native.None in
      let uu____3211 =
        resolve_in_open_namespaces' env lid
          (fun uu____3218  -> FStar_Pervasives_Native.None)
          (fun uu____3221  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____3211 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____3231 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____3248 =
        FStar_List.tryFind
          (fun uu____3259  ->
             match uu____3259 with
             | (mlid,modul) ->
                 let uu____3266 = FStar_Ident.path_of_lid mlid in
                 uu____3266 = path) env.modules in
      match uu____3248 with
      | FStar_Pervasives_Native.Some (uu____3273,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_3303 =
        match uu___163_3303 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____3310,lbs),uu____3312,uu____3313);
             FStar_Syntax_Syntax.sigrng = uu____3314;
             FStar_Syntax_Syntax.sigquals = uu____3315;
             FStar_Syntax_Syntax.sigmeta = uu____3316;_},uu____3317)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____3339 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____3339
        | uu____3340 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3345  -> FStar_Pervasives_Native.None)
        (fun uu____3346  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_3371 =
        match uu___164_3371 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____3383,uu____3384);
             FStar_Syntax_Syntax.sigrng = uu____3385;
             FStar_Syntax_Syntax.sigquals = uu____3386;
             FStar_Syntax_Syntax.sigmeta = uu____3387;_},uu____3388)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____3417 -> FStar_Pervasives_Native.None)
        | uu____3426 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3439  -> FStar_Pervasives_Native.None)
        (fun uu____3444  -> FStar_Pervasives_Native.None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____3485 = try_lookup_name any_val exclude_interf env lid in
          match uu____3485 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____3500 -> FStar_Pervasives_Native.None
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3527 = try_lookup_lid env l in
      match uu____3527 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____3541) ->
          let uu____3546 =
            let uu____3547 = FStar_Syntax_Subst.compress e in
            uu____3547.FStar_Syntax_Syntax.n in
          (match uu____3546 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____3559 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___182_3573 = env in
        {
          curmodule = (uu___182_3573.curmodule);
          curmonad = (uu___182_3573.curmonad);
          modules = (uu___182_3573.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___182_3573.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___182_3573.sigaccum);
          sigmap = (uu___182_3573.sigmap);
          iface = (uu___182_3573.iface);
          admitted_iface = (uu___182_3573.admitted_iface);
          expect_typ = (uu___182_3573.expect_typ);
          docs = (uu___182_3573.docs);
          remaining_iface_decls = (uu___182_3573.remaining_iface_decls);
          syntax_only = (uu___182_3573.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_3602 =
        match uu___166_3602 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3609,uu____3610,uu____3611);
             FStar_Syntax_Syntax.sigrng = uu____3612;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3614;_},uu____3615)
            ->
            let uu____3618 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___165_3621  ->
                      match uu___165_3621 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____3622 -> false)) in
            if uu____3618
            then
              let uu____3625 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____3625
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____3627;
             FStar_Syntax_Syntax.sigrng = uu____3628;
             FStar_Syntax_Syntax.sigquals = uu____3629;
             FStar_Syntax_Syntax.sigmeta = uu____3630;_},uu____3631)
            ->
            let uu____3648 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____3648
        | uu____3649 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3654  -> FStar_Pervasives_Native.None)
        (fun uu____3655  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___167_3680 =
        match uu___167_3680 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____3689,uu____3690,uu____3691,uu____3692,datas,uu____3694);
             FStar_Syntax_Syntax.sigrng = uu____3695;
             FStar_Syntax_Syntax.sigquals = uu____3696;
             FStar_Syntax_Syntax.sigmeta = uu____3697;_},uu____3698)
            -> FStar_Pervasives_Native.Some datas
        | uu____3711 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3720  -> FStar_Pervasives_Native.None)
        (fun uu____3723  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit,Prims.unit -> Prims.unit)
     FStar_Pervasives_Native.tuple5,Prims.unit -> Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____3772 =
    let uu____3773 =
      let uu____3778 =
        let uu____3781 = FStar_ST.read record_cache in
        FStar_List.hd uu____3781 in
      let uu____3794 = FStar_ST.read record_cache in uu____3778 :: uu____3794 in
    FStar_ST.write record_cache uu____3773 in
  let pop1 uu____3816 =
    let uu____3817 =
      let uu____3822 = FStar_ST.read record_cache in FStar_List.tl uu____3822 in
    FStar_ST.write record_cache uu____3817 in
  let peek uu____3846 =
    let uu____3847 = FStar_ST.read record_cache in FStar_List.hd uu____3847 in
  let insert r =
    let uu____3864 =
      let uu____3869 = let uu____3872 = peek () in r :: uu____3872 in
      let uu____3875 =
        let uu____3880 = FStar_ST.read record_cache in
        FStar_List.tl uu____3880 in
      uu____3869 :: uu____3875 in
    FStar_ST.write record_cache uu____3864 in
  let commit1 uu____3904 =
    let uu____3905 = FStar_ST.read record_cache in
    match uu____3905 with
    | hd1::uu____3917::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____3939 -> failwith "Impossible" in
  let filter1 uu____3947 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____3956 =
           let uu____3961 = FStar_ST.read record_cache in filtered ::
             uu____3961 in
         FStar_ST.write record_cache uu____3956) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit,
    Prims.unit -> Prims.unit) FStar_Pervasives_Native.tuple5
  =
  let uu____4061 = record_cache_aux_with_filter in
  match uu____4061 with | (aux,uu____4113) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____4164 = record_cache_aux_with_filter in
  match uu____4164 with | (uu____4195,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____4247 = record_cache_aux in
  match uu____4247 with
  | (push1,uu____4273,uu____4274,uu____4275,uu____4276) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____4303 = record_cache_aux in
  match uu____4303 with
  | (uu____4328,pop1,uu____4330,uu____4331,uu____4332) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____4361 = record_cache_aux in
  match uu____4361 with
  | (uu____4388,uu____4389,peek,uu____4391,uu____4392) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____4419 = record_cache_aux in
  match uu____4419 with
  | (uu____4444,uu____4445,uu____4446,insert,uu____4448) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____4475 = record_cache_aux in
  match uu____4475 with
  | (uu____4500,uu____4501,uu____4502,uu____4503,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____4549) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___168_4563  ->
                   match uu___168_4563 with
                   | FStar_Syntax_Syntax.RecordType uu____4564 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____4573 -> true
                   | uu____4582 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___169_4593  ->
                      match uu___169_4593 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____4595,uu____4596,uu____4597,uu____4598,uu____4599);
                          FStar_Syntax_Syntax.sigrng = uu____4600;
                          FStar_Syntax_Syntax.sigquals = uu____4601;
                          FStar_Syntax_Syntax.sigmeta = uu____4602;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____4609 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___170_4612  ->
                    match uu___170_4612 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____4616,uu____4617,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____4619;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____4621;_} ->
                        let uu____4630 =
                          let uu____4631 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____4631 in
                        (match uu____4630 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____4637,t,uu____4639,uu____4640,uu____4641);
                             FStar_Syntax_Syntax.sigrng = uu____4642;
                             FStar_Syntax_Syntax.sigquals = uu____4643;
                             FStar_Syntax_Syntax.sigmeta = uu____4644;_} ->
                             let uu____4651 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____4651 with
                              | (formals,uu____4667) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____4716  ->
                                            match uu____4716 with
                                            | (x,q) ->
                                                let uu____4729 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____4729
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____4788  ->
                                            match uu____4788 with
                                            | (x,q) ->
                                                let uu____4803 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____4803,
                                                  (x.FStar_Syntax_Syntax.sort)))) in
                                  let fields = fields' in
                                  let record =
                                    {
                                      typename;
                                      constrname =
                                        (constrname.FStar_Ident.ident);
                                      parms;
                                      fields;
                                      is_private_or_abstract =
                                        ((FStar_List.contains
                                            FStar_Syntax_Syntax.Private
                                            typename_quals)
                                           ||
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Abstract
                                              typename_quals));
                                      is_record = is_rec
                                    } in
                                  ((let uu____4822 =
                                      let uu____4825 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____4825 in
                                    FStar_ST.write new_globs uu____4822);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____4848 =
                                            match uu____4848 with
                                            | (id,uu____4858) ->
                                                let modul =
                                                  let uu____4868 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____4868.FStar_Ident.str in
                                                let uu____4869 =
                                                  get_exported_id_set e modul in
                                                (match uu____4869 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____4890 =
                                                         let uu____4891 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____4891 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____4890);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____4899 =
                                                               let uu____4900
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____4900.FStar_Ident.ident in
                                                             uu____4899.FStar_Ident.idText in
                                                           let uu____4902 =
                                                             let uu____4903 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____4903 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____4902))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____4922 -> ())
                    | uu____4923 -> ()))
        | uu____4924 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____4939 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____4939 with
        | (ns,id) ->
            let uu____4956 = peek_record_cache () in
            FStar_Util.find_map uu____4956
              (fun record  ->
                 let uu____4960 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____4964  -> FStar_Pervasives_Native.None)
                   uu____4960) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____4965  -> Cont_ignore) (fun uu____4966  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____4969 = find_in_cache fn in
           cont_of_option Cont_ignore uu____4969)
        (fun k  -> fun uu____4973  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____4984 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4984 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____4990 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____5002 = try_lookup_record_by_field_name env lid in
        match uu____5002 with
        | FStar_Pervasives_Native.Some record' when
            let uu____5006 =
              let uu____5007 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____5007 in
            let uu____5010 =
              let uu____5011 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____5011 in
            uu____5006 = uu____5010 ->
            let uu____5014 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____5017  -> Cont_ok ()) in
            (match uu____5014 with
             | Cont_ok uu____5018 -> true
             | uu____5019 -> false)
        | uu____5022 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____5037 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____5037 with
      | FStar_Pervasives_Native.Some r ->
          let uu____5047 =
            let uu____5052 =
              let uu____5053 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____5053
                (FStar_Ident.range_of_lid fieldname) in
            (uu____5052, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____5047
      | uu____5058 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____5072  ->
    let uu____5073 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____5073
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____5087  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___171_5098  ->
      match uu___171_5098 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___172_5120 =
            match uu___172_5120 with
            | Rec_binding uu____5121 -> true
            | uu____5122 -> false in
          let this_env =
            let uu___183_5124 = env in
            let uu____5125 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___183_5124.curmodule);
              curmonad = (uu___183_5124.curmonad);
              modules = (uu___183_5124.modules);
              scope_mods = uu____5125;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___183_5124.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___183_5124.sigaccum);
              sigmap = (uu___183_5124.sigmap);
              iface = (uu___183_5124.iface);
              admitted_iface = (uu___183_5124.admitted_iface);
              expect_typ = (uu___183_5124.expect_typ);
              docs = (uu___183_5124.docs);
              remaining_iface_decls = (uu___183_5124.remaining_iface_decls);
              syntax_only = (uu___183_5124.syntax_only)
            } in
          let uu____5128 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____5128 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____5139 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___184_5154 = env in
      {
        curmodule = (uu___184_5154.curmodule);
        curmonad = (uu___184_5154.curmonad);
        modules = (uu___184_5154.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___184_5154.exported_ids);
        trans_exported_ids = (uu___184_5154.trans_exported_ids);
        includes = (uu___184_5154.includes);
        sigaccum = (uu___184_5154.sigaccum);
        sigmap = (uu___184_5154.sigmap);
        iface = (uu___184_5154.iface);
        admitted_iface = (uu___184_5154.admitted_iface);
        expect_typ = (uu___184_5154.expect_typ);
        docs = (uu___184_5154.docs);
        remaining_iface_decls = (uu___184_5154.remaining_iface_decls);
        syntax_only = (uu___184_5154.syntax_only)
      }
let push_bv':
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
            FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x true
let push_bv:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____5199 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____5199
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err1 l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____5224) ->
              let uu____5229 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____5229 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____5237 =
          let uu____5238 =
            let uu____5243 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____5243, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____5238 in
        raise uu____5237 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____5252 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____5261 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____5272 -> (true, true)
          | uu____5281 -> (false, false) in
        match uu____5252 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____5287 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____5291 =
                     let uu____5292 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____5292 in
                   if uu____5291
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____5287 with
             | FStar_Pervasives_Native.Some l when
                 let uu____5297 = FStar_Options.interactive () in
                 Prims.op_Negation uu____5297 -> err1 l
             | uu____5298 ->
                 (extract_record env globals s;
                  (let uu___185_5304 = env in
                   {
                     curmodule = (uu___185_5304.curmodule);
                     curmonad = (uu___185_5304.curmonad);
                     modules = (uu___185_5304.modules);
                     scope_mods = (uu___185_5304.scope_mods);
                     exported_ids = (uu___185_5304.exported_ids);
                     trans_exported_ids = (uu___185_5304.trans_exported_ids);
                     includes = (uu___185_5304.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___185_5304.sigmap);
                     iface = (uu___185_5304.iface);
                     admitted_iface = (uu___185_5304.admitted_iface);
                     expect_typ = (uu___185_5304.expect_typ);
                     docs = (uu___185_5304.docs);
                     remaining_iface_decls =
                       (uu___185_5304.remaining_iface_decls);
                     syntax_only = (uu___185_5304.syntax_only)
                   }))) in
      let env2 =
        let uu___186_5306 = env1 in
        let uu____5307 = FStar_ST.read globals in
        {
          curmodule = (uu___186_5306.curmodule);
          curmonad = (uu___186_5306.curmonad);
          modules = (uu___186_5306.modules);
          scope_mods = uu____5307;
          exported_ids = (uu___186_5306.exported_ids);
          trans_exported_ids = (uu___186_5306.trans_exported_ids);
          includes = (uu___186_5306.includes);
          sigaccum = (uu___186_5306.sigaccum);
          sigmap = (uu___186_5306.sigmap);
          iface = (uu___186_5306.iface);
          admitted_iface = (uu___186_5306.admitted_iface);
          expect_typ = (uu___186_5306.expect_typ);
          docs = (uu___186_5306.docs);
          remaining_iface_decls = (uu___186_5306.remaining_iface_decls);
          syntax_only = (uu___186_5306.syntax_only)
        } in
      let uu____5314 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5340) ->
            let uu____5349 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____5349)
        | uu____5375 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____5314 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____5431  ->
                   match uu____5431 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____5448 =
                                  let uu____5451 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____5451 in
                                FStar_ST.write globals uu____5448);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____5463 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____5463.FStar_Ident.str in
                                    ((let uu____5465 =
                                        get_exported_id_set env3 modul in
                                      match uu____5465 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____5485 =
                                            let uu____5486 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____5486 in
                                          FStar_ST.write my_exported_ids
                                            uu____5485
                                      | FStar_Pervasives_Native.None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___187_5502 = env3 in
              let uu____5503 = FStar_ST.read globals in
              {
                curmodule = (uu___187_5502.curmodule);
                curmonad = (uu___187_5502.curmonad);
                modules = (uu___187_5502.modules);
                scope_mods = uu____5503;
                exported_ids = (uu___187_5502.exported_ids);
                trans_exported_ids = (uu___187_5502.trans_exported_ids);
                includes = (uu___187_5502.includes);
                sigaccum = (uu___187_5502.sigaccum);
                sigmap = (uu___187_5502.sigmap);
                iface = (uu___187_5502.iface);
                admitted_iface = (uu___187_5502.admitted_iface);
                expect_typ = (uu___187_5502.expect_typ);
                docs = (uu___187_5502.docs);
                remaining_iface_decls = (uu___187_5502.remaining_iface_decls);
                syntax_only = (uu___187_5502.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____5516 =
        let uu____5521 = resolve_module_name env ns false in
        match uu____5521 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____5535 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____5546  ->
                      match uu____5546 with
                      | (m,uu____5552) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____5535
            then (ns, Open_namespace)
            else
              (let uu____5558 =
                 let uu____5559 =
                   let uu____5564 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____5564, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____5559 in
               raise uu____5558)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____5516 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____5580 = resolve_module_name env ns false in
      match uu____5580 with
      | FStar_Pervasives_Native.Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____5587 = current_module env1 in
              uu____5587.FStar_Ident.str in
            (let uu____5589 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____5589 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____5613 =
                   let uu____5616 = FStar_ST.read incl in ns1 :: uu____5616 in
                 FStar_ST.write incl uu____5613);
            (match () with
             | () ->
                 let uu____5627 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____5627 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____5644 =
                          let uu____5661 = get_exported_id_set env1 curmod in
                          let uu____5668 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____5661, uu____5668) in
                        match uu____5644 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____5722 = ns_trans_exports k in
                                FStar_ST.read uu____5722 in
                              let ex = cur_exports k in
                              (let uu____5733 =
                                 let uu____5734 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____5734 ns_ex in
                               FStar_ST.write ex uu____5733);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____5746 =
                                     let uu____5747 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____5747 ns_ex in
                                   FStar_ST.write trans_ex uu____5746) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____5754 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5775 =
                        let uu____5776 =
                          let uu____5781 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____5781, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____5776 in
                      raise uu____5775))))
      | uu____5782 ->
          let uu____5785 =
            let uu____5786 =
              let uu____5791 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____5791, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____5786 in
          raise uu____5785
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____5801 = module_is_defined env l in
        if uu____5801
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____5804 =
             let uu____5805 =
               let uu____5810 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____5810, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____5805 in
           raise uu____5804)
let push_doc:
  env ->
    FStar_Ident.lid ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____5826 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____5826 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____5830 =
                    let uu____5831 = FStar_Ident.string_of_lid l in
                    let uu____5832 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____5833 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____5831 uu____5832 uu____5833 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____5830);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____5842 = try_lookup_lid env l in
                (match uu____5842 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5854 =
                         let uu____5855 = FStar_Options.interactive () in
                         Prims.op_Negation uu____5855 in
                       if uu____5854
                       then
                         let uu____5856 =
                           let uu____5857 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____5858 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____5857 uu____5858 in
                         FStar_Util.print_string uu____5856
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___188_5867 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___188_5867.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___188_5867.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___188_5867.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____5868 -> ())
            | uu____5877 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5890) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1  ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____5903,uu____5904,uu____5905,uu____5906,uu____5907)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____5916 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____5919,uu____5920) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____5926,lbs),uu____5928,uu____5929) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____5952 =
                               let uu____5953 =
                                 let uu____5954 =
                                   let uu____5963 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____5963.FStar_Syntax_Syntax.fv_name in
                                 uu____5954.FStar_Syntax_Syntax.v in
                               uu____5953.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____5952))
                   else ();
                   if
                     (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                       &&
                       (Prims.op_Negation
                          (FStar_List.contains FStar_Syntax_Syntax.Private
                             quals))
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let lid =
                               let uu____5977 =
                                 let uu____5986 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____5986.FStar_Syntax_Syntax.fv_name in
                               uu____5977.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___189_5995 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___189_5995.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___189_5995.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____6007 -> ()));
      (let curmod =
         let uu____6009 = current_module env in uu____6009.FStar_Ident.str in
       (let uu____6011 =
          let uu____6028 = get_exported_id_set env curmod in
          let uu____6035 = get_trans_exported_id_set env curmod in
          (uu____6028, uu____6035) in
        match uu____6011 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____6089 = cur_ex eikind in FStar_ST.read uu____6089 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____6099 =
                let uu____6100 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____6100 in
              FStar_ST.write cur_trans_ex_set_ref uu____6099 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____6107 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___190_6125 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___190_6125.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___190_6125.exported_ids);
                    trans_exported_ids = (uu___190_6125.trans_exported_ids);
                    includes = (uu___190_6125.includes);
                    sigaccum = [];
                    sigmap = (uu___190_6125.sigmap);
                    iface = (uu___190_6125.iface);
                    admitted_iface = (uu___190_6125.admitted_iface);
                    expect_typ = (uu___190_6125.expect_typ);
                    docs = (uu___190_6125.docs);
                    remaining_iface_decls =
                      (uu___190_6125.remaining_iface_decls);
                    syntax_only = (uu___190_6125.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____6142 =
       let uu____6145 = FStar_ST.read stack in env :: uu____6145 in
     FStar_ST.write stack uu____6142);
    (let uu___191_6152 = env in
     let uu____6153 = FStar_Util.smap_copy (sigmap env) in
     let uu____6164 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___191_6152.curmodule);
       curmonad = (uu___191_6152.curmonad);
       modules = (uu___191_6152.modules);
       scope_mods = (uu___191_6152.scope_mods);
       exported_ids = (uu___191_6152.exported_ids);
       trans_exported_ids = (uu___191_6152.trans_exported_ids);
       includes = (uu___191_6152.includes);
       sigaccum = (uu___191_6152.sigaccum);
       sigmap = uu____6153;
       iface = (uu___191_6152.iface);
       admitted_iface = (uu___191_6152.admitted_iface);
       expect_typ = (uu___191_6152.expect_typ);
       docs = uu____6164;
       remaining_iface_decls = (uu___191_6152.remaining_iface_decls);
       syntax_only = (uu___191_6152.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____6169  ->
    let uu____6170 = FStar_ST.read stack in
    match uu____6170 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____6183 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____6190 = FStar_ST.read stack in
     match uu____6190 with
     | uu____6195::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____6202 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____6210  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____6222 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____6225 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____6254 = FStar_Util.smap_try_find sm' k in
              match uu____6254 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___192_6279 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___192_6279.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___192_6279.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___192_6279.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____6280 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____6285 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
let prepare_module_or_interface:
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> (env,Prims.bool) FStar_Pervasives_Native.tuple2
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          let prep env1 =
            let filename =
              FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
            let auto_open = FStar_Parser_Dep.hard_coded_dependencies filename in
            let auto_open1 =
              let convert_kind uu___173_6338 =
                match uu___173_6338 with
                | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                | FStar_Parser_Dep.Open_module  -> Open_module in
              FStar_List.map
                (fun uu____6347  ->
                   match uu____6347 with
                   | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
            let namespace_of_module =
              if
                (FStar_List.length mname.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                let uu____6371 =
                  let uu____6376 =
                    FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                  (uu____6376, Open_namespace) in
                [uu____6371]
              else [] in
            let auto_open2 =
              FStar_List.rev
                (FStar_List.append auto_open1 namespace_of_module) in
            (let uu____6406 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____6406);
            (match () with
             | () ->
                 ((let uu____6410 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____6410);
                  (match () with
                   | () ->
                       ((let uu____6414 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____6414);
                        (match () with
                         | () ->
                             let uu___193_6427 = env1 in
                             let uu____6428 =
                               FStar_List.map
                                 (fun x  -> Open_module_or_namespace x)
                                 auto_open2 in
                             {
                               curmodule =
                                 (FStar_Pervasives_Native.Some mname);
                               curmonad = (uu___193_6427.curmonad);
                               modules = (uu___193_6427.modules);
                               scope_mods = uu____6428;
                               exported_ids = (uu___193_6427.exported_ids);
                               trans_exported_ids =
                                 (uu___193_6427.trans_exported_ids);
                               includes = (uu___193_6427.includes);
                               sigaccum = (uu___193_6427.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___193_6427.expect_typ);
                               docs = (uu___193_6427.docs);
                               remaining_iface_decls =
                                 (uu___193_6427.remaining_iface_decls);
                               syntax_only = (uu___193_6427.syntax_only)
                             }))))) in
          let uu____6432 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____6455  ->
                    match uu____6455 with
                    | (l,uu____6461) -> FStar_Ident.lid_equals l mname)) in
          match uu____6432 with
          | FStar_Pervasives_Native.None  ->
              let uu____6470 = prep env in (uu____6470, false)
          | FStar_Pervasives_Native.Some (uu____6471,m) ->
              ((let uu____6478 =
                  (let uu____6479 = FStar_Options.interactive () in
                   Prims.op_Negation uu____6479) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____6478
                then
                  let uu____6480 =
                    let uu____6481 =
                      let uu____6486 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____6486, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____6481 in
                  raise uu____6480
                else ());
               (let uu____6488 = let uu____6489 = push env in prep uu____6489 in
                (uu____6488, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.None  ->
          let uu___194_6497 = env in
          {
            curmodule = (uu___194_6497.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___194_6497.modules);
            scope_mods = (uu___194_6497.scope_mods);
            exported_ids = (uu___194_6497.exported_ids);
            trans_exported_ids = (uu___194_6497.trans_exported_ids);
            includes = (uu___194_6497.includes);
            sigaccum = (uu___194_6497.sigaccum);
            sigmap = (uu___194_6497.sigmap);
            iface = (uu___194_6497.iface);
            admitted_iface = (uu___194_6497.admitted_iface);
            expect_typ = (uu___194_6497.expect_typ);
            docs = (uu___194_6497.docs);
            remaining_iface_decls = (uu___194_6497.remaining_iface_decls);
            syntax_only = (uu___194_6497.syntax_only)
          }
let fail_or env lookup lid =
  let uu____6524 = lookup lid in
  match uu____6524 with
  | FStar_Pervasives_Native.None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____6534  ->
             match uu____6534 with
             | (lid1,uu____6540) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____6545 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____6545
               (FStar_Ident.range_of_lid lid) in
           let uu____6546 = resolve_module_name env modul true in
           match uu____6546 with
           | FStar_Pervasives_Native.None  ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format3
                 "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str opened_modules1
           | FStar_Pervasives_Native.Some modul' when
               Prims.op_Negation
                 (FStar_List.existsb (fun m  -> m = modul'.FStar_Ident.str)
                    opened_modules)
               ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 opened_modules1
           | FStar_Pervasives_Native.Some modul' ->
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, definition %s not found"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 (lid.FStar_Ident.ident).FStar_Ident.idText) in
      raise (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
  | FStar_Pervasives_Native.Some r -> r
let fail_or2 lookup id =
  let uu____6576 = lookup id in
  match uu____6576 with
  | FStar_Pervasives_Native.None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | FStar_Pervasives_Native.Some r -> r