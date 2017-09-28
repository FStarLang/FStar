open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut[@@deriving show]
let uu___is_VerifyAll: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____5 -> false
let uu___is_VerifyUserList: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____10 -> false
let uu___is_VerifyFigureItOut: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____15 -> false
type map =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White
  | Gray
  | Black[@@deriving show]
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____30 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____35 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____40 -> false
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____45 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____50 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____77 =
             (l > lext) &&
               (let uu____89 = FStar_String.substring f (l - lext) lext in
                uu____89 = ext) in
           if uu____77
           then
             let uu____106 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____106
           else FStar_Pervasives_Native.None) suffixes in
    let uu____118 = FStar_List.filter FStar_Util.is_some matches in
    match uu____118 with
    | (FStar_Pervasives_Native.Some m)::uu____128 ->
        FStar_Pervasives_Native.Some m
    | uu____135 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____144 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____144 = 105
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____149 = is_interface f in Prims.op_Negation uu____149
let list_of_option:
  'Auu____154 .
    'Auu____154 FStar_Pervasives_Native.option -> 'Auu____154 Prims.list
  =
  fun uu___82_162  ->
    match uu___82_162 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____170 .
    ('Auu____170 FStar_Pervasives_Native.option,'Auu____170
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____170 Prims.list
  =
  fun uu____184  ->
    match uu____184 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____207 =
      let uu____210 = FStar_Util.basename f in
      check_and_strip_suffix uu____210 in
    match uu____207 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____212 =
          let uu____213 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____213 in
        FStar_Exn.raise uu____212
let build_map: Prims.string Prims.list -> map =
  fun filenames  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____232 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____232 in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____259 = FStar_Util.smap_try_find map1 key in
      match uu____259 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____296 = is_interface full_path in
          if uu____296
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____330 = is_interface full_path in
          if uu____330
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    FStar_List.iter
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.iter
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____371 = check_and_strip_suffix f1 in
                match uu____371 with
                | FStar_Pervasives_Native.Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1 in
                    let key = FStar_String.lowercase longname in
                    add_entry key full_path
                | FStar_Pervasives_Native.None  -> ()) files
         else
           (let uu____379 =
              let uu____380 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____380 in
            FStar_Exn.raise uu____379)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____385 = lowercase_module_name f in add_entry uu____385 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____403 =
           let uu____406 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____406 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____432 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____432 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____403);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____606 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____606 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____619 = string_of_lid l last1 in
      FStar_String.lowercase uu____619
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____624 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____624
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____636 =
        let uu____637 =
          let uu____638 =
            let uu____639 =
              let uu____642 = FStar_Util.basename filename in
              check_and_strip_suffix uu____642 in
            FStar_Util.must uu____639 in
          FStar_String.lowercase uu____638 in
        uu____637 <> k' in
      if uu____636
      then
        let uu____643 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____643 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____649 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____664 = FStar_Options.prims_basename () in
      let uu____665 =
        let uu____668 = FStar_Options.pervasives_basename () in
        let uu____669 =
          let uu____672 = FStar_Options.pervasives_native_basename () in
          [uu____672] in
        uu____668 :: uu____669 in
      uu____664 :: uu____665 in
    if FStar_List.mem filename1 corelibs
    then []
    else
      [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
      (FStar_Parser_Const.prims_lid, Open_module);
      (FStar_Parser_Const.pervasives_lid, Open_module)]
let collect_one:
  (Prims.string,Prims.bool FStar_ST.ref) FStar_Pervasives_Native.tuple2
    Prims.list ->
    verify_mode ->
      Prims.bool -> map -> Prims.string -> Prims.string Prims.list
  =
  fun verify_flags  ->
    fun verify_mode  ->
      fun is_user_provided_filename  ->
        fun original_map  ->
          fun filename  ->
            let deps = FStar_Util.mk_ref [] in
            let add_dep d =
              let uu____751 =
                let uu____752 =
                  let uu____753 = FStar_ST.op_Bang deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____753 in
                Prims.op_Negation uu____752 in
              if uu____751
              then
                let uu____822 =
                  let uu____825 = FStar_ST.op_Bang deps in d :: uu____825 in
                FStar_ST.op_Colon_Equals deps uu____822
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____984 = FStar_Util.smap_try_find working_map key in
              match uu____984 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____1024 = lowercase_module_name f in
                        add_dep uu____1024) (list_of_pair pair);
                   true)
              | FStar_Pervasives_Native.None  ->
                  let r = enter_namespace original_map working_map key in
                  (if Prims.op_Negation r
                   then
                     (if let_open
                      then
                        FStar_Exn.raise
                          (FStar_Errors.Err
                             "let-open only supported for modules, not namespaces")
                      else
                        (let uu____1036 = string_of_lid lid true in
                         FStar_Util.print2_warning
                           "Warning: in %s: no modules in namespace %s and no file with that name either\n"
                           filename uu____1036))
                   else ();
                   false) in
            let record_open_namespace error_msg lid =
              let key = lowercase_join_longident lid true in
              let r = enter_namespace original_map working_map key in
              if Prims.op_Negation r
              then
                match error_msg with
                | FStar_Pervasives_Native.Some e ->
                    FStar_Exn.raise (FStar_Errors.Err e)
                | FStar_Pervasives_Native.None  ->
                    let uu____1052 = string_of_lid lid true in
                    FStar_Util.print1_warning
                      "Warning: no modules in namespace %s and no file with that name either\n"
                      uu____1052
              else () in
            let record_open let_open lid =
              let uu____1061 = record_open_module let_open lid in
              if uu____1061
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____1076 =
              match uu____1076 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____1083 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____1093 = FStar_Util.smap_try_find original_map alias in
              match uu____1093 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____1145 =
                    let uu____1146 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____1146 in
                  FStar_Exn.raise uu____1145 in
            let record_lid lid =
              let try_key key =
                let uu____1155 = FStar_Util.smap_try_find working_map key in
                match uu____1155 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____1194 = lowercase_module_name f in
                         add_dep uu____1194) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____1203 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____1203
                    then
                      let uu____1204 =
                        let uu____1205 = string_of_lid lid false in
                        FStar_Util.format1 "Unbound module reference %s"
                          uu____1205 in
                      FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                        uu____1204
                    else () in
              let uu____1208 = lowercase_join_longident lid false in
              try_key uu____1208 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_module uu___83_1293 =
               match uu___83_1293 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1302 =
                         let uu____1303 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1303 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1306 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1306
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1307 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1307
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1411  ->
                              match uu____1411 with
                              | (m,r) ->
                                  let uu____1700 =
                                    let uu____1701 =
                                      let uu____1702 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1702 in
                                    (FStar_String.lowercase m) = uu____1701 in
                                  if uu____1700
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____1848) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1855 =
                         let uu____1856 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1856 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1859 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1859
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1860 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1860
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1964  ->
                              match uu____1964 with
                              | (m,r) ->
                                  let uu____2253 =
                                    let uu____2254 =
                                      let uu____2255 = string_of_lid lid true in
                                      FStar_String.lowercase uu____2255 in
                                    (FStar_String.lowercase m) = uu____2254 in
                                  if uu____2253
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___84_2406 =
               match uu___84_2406 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____2412 = lowercase_join_longident lid true in
                     add_dep uu____2412);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____2413,patterms) ->
                   FStar_List.iter
                     (fun uu____2435  ->
                        match uu____2435 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____2444,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2446;
                     FStar_Parser_AST.mdest = uu____2447;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2449;
                     FStar_Parser_AST.mdest = uu____2450;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____2452,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2454;
                     FStar_Parser_AST.mdest = uu____2455;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____2459,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____2489  ->
                          match uu____2489 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____2502,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____2509 -> ()
               | FStar_Parser_AST.Pragma uu____2510 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____2534 =
                       let uu____2535 = FStar_ST.op_Bang num_of_toplevelmods in
                       uu____2535 > (Prims.parse_int "1") in
                     if uu____2534
                     then
                       let uu____2596 =
                         let uu____2597 =
                           let uu____2598 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____2598 in
                         FStar_Errors.Err uu____2597 in
                       FStar_Exn.raise uu____2596
                     else ()))
             and collect_tycon uu___85_2600 =
               match uu___85_2600 with
               | FStar_Parser_AST.TyconAbstract (uu____2601,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____2613,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____2627,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2673  ->
                         match uu____2673 with
                         | (uu____2682,t,uu____2684) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____2689,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2748  ->
                         match uu____2748 with
                         | (uu____2761,t,uu____2763,uu____2764) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___86_2773 =
               match uu___86_2773 with
               | FStar_Parser_AST.DefineEffect (uu____2774,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____2788,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___87_2799 =
               match uu___87_2799 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____2800,t);
                   FStar_Parser_AST.brange = uu____2802;
                   FStar_Parser_AST.blevel = uu____2803;
                   FStar_Parser_AST.aqual = uu____2804;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____2805,t);
                   FStar_Parser_AST.brange = uu____2807;
                   FStar_Parser_AST.blevel = uu____2808;
                   FStar_Parser_AST.aqual = uu____2809;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____2811;
                   FStar_Parser_AST.blevel = uu____2812;
                   FStar_Parser_AST.aqual = uu____2813;_} -> collect_term t
               | uu____2814 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___88_2816 =
               match uu___88_2816 with
               | FStar_Const.Const_int
                   (uu____2817,FStar_Pervasives_Native.Some
                    (signedness,width))
                   ->
                   let u =
                     match signedness with
                     | FStar_Const.Unsigned  -> "u"
                     | FStar_Const.Signed  -> "" in
                   let w =
                     match width with
                     | FStar_Const.Int8  -> "8"
                     | FStar_Const.Int16  -> "16"
                     | FStar_Const.Int32  -> "32"
                     | FStar_Const.Int64  -> "64" in
                   let uu____2832 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____2832
               | uu____2833 -> ()
             and collect_term' uu___89_2834 =
               match uu___89_2834 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____2843 =
                         let uu____2844 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____2844 in
                       collect_term' uu____2843)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____2846 -> ()
               | FStar_Parser_AST.Uvar uu____2847 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____2850) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____2880  ->
                         match uu____2880 with
                         | (t,uu____2886) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____2896) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____2898,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____2922  ->
                         match uu____2922 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____2933,t1,t2) ->
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
                      (fun uu____3029  ->
                         match uu____3029 with
                         | (uu____3034,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____3037) -> collect_term t
               | FStar_Parser_AST.Product (binders,t) ->
                   (collect_binders binders; collect_term t)
               | FStar_Parser_AST.Sum (binders,t) ->
                   (collect_binders binders; collect_term t)
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
               | FStar_Parser_AST.NamedTyp (uu____3093,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____3096,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____3099) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____3105) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____3111,uu____3112) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___90_3120 =
               match uu___90_3120 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____3121 -> ()
               | FStar_Parser_AST.PatConst uu____3122 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____3130 -> ()
               | FStar_Parser_AST.PatName uu____3137 -> ()
               | FStar_Parser_AST.PatTvar uu____3138 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____3152) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____3171  ->
                        match uu____3171 with
                        | (uu____3176,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____3200 =
               match uu____3200 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____3218 = FStar_Parser_Driver.parse_file filename in
             match uu____3218 with
             | (ast,uu____3232) ->
                 (collect_module ast; FStar_ST.op_Bang deps))
let print_graph:
  'Auu____3314 .
    (Prims.string Prims.list,'Auu____3314) FStar_Pervasives_Native.tuple2
      FStar_Util.smap -> Prims.unit
  =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____3338 =
       let uu____3339 =
         let uu____3340 =
           let uu____3341 =
             let uu____3344 =
               let uu____3347 = FStar_Util.smap_keys graph in
               FStar_List.unique uu____3347 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____3363 =
                      let uu____3370 = FStar_Util.smap_try_find graph k in
                      FStar_Util.must uu____3370 in
                    FStar_Pervasives_Native.fst uu____3363 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  FStar_List.map
                    (fun dep1  ->
                       FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
               uu____3344 in
           FStar_String.concat "\n" uu____3341 in
         Prims.strcat uu____3340 "\n}\n" in
       Prims.strcat "digraph {\n" uu____3339 in
     FStar_Util.write_file "dep.graph" uu____3338)
let collect:
  verify_mode ->
    Prims.string Prims.list ->
      ((Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
         Prims.list,Prims.string Prims.list,(Prims.string Prims.list,
                                              color)
                                              FStar_Pervasives_Native.tuple2
                                              FStar_Util.smap)
        FStar_Pervasives_Native.tuple3
  =
  fun verify_mode  ->
    fun filenames  ->
      let graph = FStar_Util.smap_create (Prims.parse_int "41") in
      let verify_flags =
        let uu____3459 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____3471 = FStar_Util.mk_ref false in (f, uu____3471))
          uu____3459 in
      let partial_discovery =
        let uu____3491 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____3491 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____3497 =
          let uu____3506 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____3506 in
        match uu____3497 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____3562) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____3594 =
          let uu____3595 = FStar_Util.smap_try_find graph key in
          uu____3595 = FStar_Pervasives_Native.None in
        if uu____3594
        then
          let uu____3624 =
            let uu____3633 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____3633 in
          match uu____3624 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____3686) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____3692) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____3699) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____3726 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____3731 = lowercase_module_name f1 in
                     uu____3731 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____3726) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____3768 =
           let uu____3775 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____3775 in
         match uu____3768 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1_warning
                     "Warning: recursive dependency on module %s\n" key;
                   (let cycle1 =
                      FStar_All.pipe_right cycle
                        (FStar_List.map file_names_of_key) in
                    FStar_Util.print1
                      "The cycle contains a subset of the modules in:\n%s \n"
                      (FStar_String.concat "\n`used by` " cycle1);
                    print_graph immediate_graph;
                    FStar_Util.print_string "\n";
                    FStar_All.exit (Prims.parse_int "1")))
              | Black  -> direct_deps
              | White  ->
                  (FStar_Util.smap_add graph key (direct_deps, Gray);
                   (let all_deps =
                      let uu____3831 =
                        let uu____3834 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____3844 = discover (key :: cycle) dep1 in
                               dep1 :: uu____3844) direct_deps in
                        FStar_List.flatten uu____3834 in
                      FStar_List.unique uu____3831 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____3857 =
                       let uu____3860 = FStar_ST.op_Bang topologically_sorted in
                       key :: uu____3860 in
                     FStar_ST.op_Colon_Equals topologically_sorted uu____3857);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____4002 =
           let uu____4011 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____4011 in
         match uu____4002 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____4047 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____4051 = lowercase_module_name f in
                       uu____4051 = k) filenames in
                Prims.op_Negation uu____4047)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____4061 = lowercase_module_name f in
                     uu____4061 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____4063) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____4085 = must_find f in FStar_List.rev uu____4085 in
       let by_target =
         let uu____4097 =
           let uu____4100 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____4100 in
         FStar_List.collect
           (fun k  ->
              let as_list = must_find k in
              let is_interleaved =
                (FStar_List.length as_list) = (Prims.parse_int "2") in
              FStar_List.map
                (fun f  ->
                   let should_append_fsti =
                     (is_implementation f) && is_interleaved in
                   let k1 = lowercase_module_name f in
                   let suffix =
                     let uu____4145 =
                       let uu____4154 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____4154 in
                     match uu____4145 with
                     | (FStar_Pervasives_Native.Some intf,uu____4184) when
                         should_append_fsti -> [intf]
                     | uu____4191 -> [] in
                   let deps =
                     let uu____4203 = discover1 k1 in
                     FStar_List.rev uu____4203 in
                   let deps_as_filenames =
                     let uu____4209 = FStar_List.collect must_find deps in
                     FStar_List.append uu____4209 suffix in
                   (f, deps_as_filenames)) as_list) uu____4097 in
       let topologically_sorted1 =
         let uu____4217 = FStar_ST.op_Bang topologically_sorted in
         FStar_List.collect must_find_r uu____4217 in
       FStar_List.iter
         (fun uu____4389  ->
            match uu____4389 with
            | (m1,r) ->
                let uu____4678 =
                  (let uu____4681 = FStar_ST.op_Bang r in
                   Prims.op_Negation uu____4681) &&
                    (let uu____4825 = FStar_Options.interactive () in
                     Prims.op_Negation uu____4825) in
                if uu____4678
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____4828 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____4836 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____4836 = ".fst") in
                    if uu____4828
                    then
                      let uu____4843 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____4843
                    else "" in
                  let uu____4851 =
                    let uu____4852 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____4852 in
                  FStar_Exn.raise uu____4851
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____4902  ->
         match uu____4902 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                 deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print:
  'a 'b .
    ((Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
       Prims.list,'a,(Prims.string Prims.list,'b)
                       FStar_Pervasives_Native.tuple2 FStar_Util.smap)
      FStar_Pervasives_Native.tuple3 -> Prims.unit
  =
  fun uu____4953  ->
    match uu____4953 with
    | (make_deps,uu____4977,graph) ->
        let uu____5011 = FStar_Options.dep () in
        (match uu____5011 with
         | FStar_Pervasives_Native.Some "make" -> print_make make_deps
         | FStar_Pervasives_Native.Some "graph" -> print_graph graph
         | FStar_Pervasives_Native.Some uu____5014 ->
             FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
         | FStar_Pervasives_Native.None  -> ())