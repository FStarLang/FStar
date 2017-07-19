open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut
let uu___is_VerifyAll: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____4 -> false
let uu___is_VerifyUserList: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____8 -> false
let uu___is_VerifyFigureItOut: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____12 -> false
type map =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap
type color =
  | White
  | Gray
  | Black
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____26 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____30 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____34 -> false
type open_kind =
  | Open_module
  | Open_namespace
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____38 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____42 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____63 =
             (l > lext) &&
               (let uu____69 = FStar_String.substring f (l - lext) lext in
                uu____69 = ext) in
           if uu____63
           then
             let uu____79 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____79
           else FStar_Pervasives_Native.None) suffixes in
    let uu____86 = FStar_List.filter FStar_Util.is_some matches in
    match uu____86 with
    | (FStar_Pervasives_Native.Some m)::uu____96 ->
        FStar_Pervasives_Native.Some m
    | uu____103 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____111 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____111 = 'i'
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____115 = is_interface f in Prims.op_Negation uu____115
let list_of_option uu___84_126 =
  match uu___84_126 with
  | FStar_Pervasives_Native.Some x -> [x]
  | FStar_Pervasives_Native.None  -> []
let list_of_pair uu____146 =
  match uu____146 with
  | (intf,impl) ->
      FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____168 =
      let uu____171 = FStar_Util.basename f in
      check_and_strip_suffix uu____171 in
    match uu____168 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____173 =
          let uu____174 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____174 in
        raise uu____173
let build_map:
  Prims.string Prims.list ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Util.smap
  =
  fun filenames  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____192 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____192 in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____219 = FStar_Util.smap_try_find map1 key in
      match uu____219 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____256 = is_interface full_path in
          if uu____256
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____290 = is_interface full_path in
          if uu____290
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
                let uu____323 = check_and_strip_suffix f1 in
                match uu____323 with
                | FStar_Pervasives_Native.Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1 in
                    let key = FStar_String.lowercase longname in
                    add_entry key full_path
                | FStar_Pervasives_Native.None  -> ()) files
         else
           (let uu____331 =
              let uu____332 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____332 in
            raise uu____331)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____335 = lowercase_module_name f in add_entry uu____335 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____350 =
           let uu____353 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____353 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____375 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____375 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.write found true)
              else ()) uu____350);
        FStar_ST.read found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____431 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____431 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____441 = string_of_lid l last1 in
      FStar_String.lowercase uu____441
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____445 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____445
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____455 =
        let uu____456 =
          let uu____457 =
            let uu____458 =
              let uu____461 = FStar_Util.basename filename in
              check_and_strip_suffix uu____461 in
            FStar_Util.must uu____458 in
          FStar_String.lowercase uu____457 in
        uu____456 <> k' in
      if uu____455
      then
        let uu____462 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____462 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____467 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____481 = FStar_Options.prims_basename () in
      let uu____482 =
        let uu____485 = FStar_Options.pervasives_basename () in
        let uu____486 =
          let uu____489 = FStar_Options.pervasives_native_basename () in
          [uu____489] in
        uu____485 :: uu____486 in
      uu____481 :: uu____482 in
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
              let uu____563 =
                let uu____564 =
                  let uu____565 = FStar_ST.read deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____565 in
                Prims.op_Negation uu____564 in
              if uu____563
              then
                let uu____573 =
                  let uu____576 = FStar_ST.read deps in d :: uu____576 in
                FStar_ST.write deps uu____573
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____615 = FStar_Util.smap_try_find working_map key in
              match uu____615 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____653 = lowercase_module_name f in
                        add_dep uu____653) (list_of_pair pair);
                   true)
              | FStar_Pervasives_Native.None  ->
                  let r = enter_namespace original_map working_map key in
                  (if Prims.op_Negation r
                   then
                     (if let_open
                      then
                        raise
                          (FStar_Errors.Err
                             "let-open only supported for modules, not namespaces")
                      else
                        (let uu____665 = string_of_lid lid true in
                         FStar_Util.print2_warning
                           "Warning: in %s: no modules in namespace %s and no file with that name either\n"
                           filename uu____665))
                   else ();
                   false) in
            let record_open_namespace error_msg lid =
              let key = lowercase_join_longident lid true in
              let r = enter_namespace original_map working_map key in
              if Prims.op_Negation r
              then
                match error_msg with
                | FStar_Pervasives_Native.Some e ->
                    raise (FStar_Errors.Err e)
                | FStar_Pervasives_Native.None  ->
                    let uu____681 = string_of_lid lid true in
                    FStar_Util.print1_warning
                      "Warning: no modules in namespace %s and no file with that name either\n"
                      uu____681
              else () in
            let record_open let_open lid =
              let uu____690 = record_open_module let_open lid in
              if uu____690
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____705 =
              match uu____705 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____712 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____722 = FStar_Util.smap_try_find original_map alias in
              match uu____722 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____774 =
                    let uu____775 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____775 in
                  raise uu____774 in
            let record_lid lid =
              let try_key key =
                let uu____784 = FStar_Util.smap_try_find working_map key in
                match uu____784 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____821 = lowercase_module_name f in
                         add_dep uu____821) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____830 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____830
                    then
                      let uu____831 =
                        FStar_Range.string_of_range
                          (FStar_Ident.range_of_lid lid) in
                      let uu____832 = string_of_lid lid false in
                      FStar_Util.print2_warning
                        "%s (Warning): unbound module reference %s\n"
                        uu____831 uu____832
                    else () in
              let uu____835 = lowercase_join_longident lid false in
              try_key uu____835 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_fragment uu___85_936 =
               match uu___85_936 with
               | FStar_Util.Inl file -> collect_file file
               | FStar_Util.Inr decls -> collect_decls decls
             and collect_file uu___86_959 =
               match uu___86_959 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.print1_warning
                      "Warning: file %s does not respect the one module per file convention\n"
                      filename;
                    FStar_List.iter collect_module modules)
             and collect_module uu___87_967 =
               match uu___87_967 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____976 =
                         let uu____977 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____977 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____980 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____980
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____981 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____981
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____989  ->
                              match uu____989 with
                              | (m,r) ->
                                  let uu____1002 =
                                    let uu____1003 =
                                      let uu____1004 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1004 in
                                    (FStar_String.lowercase m) = uu____1003 in
                                  if uu____1002
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____1010) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1017 =
                         let uu____1018 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1018 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1021 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1021
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1022 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1022
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1030  ->
                              match uu____1030 with
                              | (m,r) ->
                                  let uu____1043 =
                                    let uu____1044 =
                                      let uu____1045 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1045 in
                                    (FStar_String.lowercase m) = uu____1044 in
                                  if uu____1043
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___88_1054 =
               match uu___88_1054 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____1060 = lowercase_join_longident lid true in
                     add_dep uu____1060);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____1061,patterms) ->
                   FStar_List.iter
                     (fun uu____1079  ->
                        match uu____1079 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____1088,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____1090;
                     FStar_Parser_AST.mdest = uu____1091;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____1093;
                     FStar_Parser_AST.mdest = uu____1094;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____1096,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____1098;
                     FStar_Parser_AST.mdest = uu____1099;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____1103,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____1130  ->
                          match uu____1130 with | (x,doc1) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____1143,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____1150 -> ()
               | FStar_Parser_AST.Pragma uu____1151 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____1157 =
                       let uu____1158 = FStar_ST.read num_of_toplevelmods in
                       uu____1158 > (Prims.parse_int "1") in
                     if uu____1157
                     then
                       let uu____1161 =
                         let uu____1162 =
                           let uu____1163 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____1163 in
                         FStar_Errors.Err uu____1162 in
                       raise uu____1161
                     else ()))
             and collect_tycon uu___89_1165 =
               match uu___89_1165 with
               | FStar_Parser_AST.TyconAbstract (uu____1166,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____1178,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____1192,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____1234  ->
                         match uu____1234 with
                         | (uu____1243,t,uu____1245) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____1250,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____1304  ->
                         match uu____1304 with
                         | (uu____1317,t,uu____1319,uu____1320) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___90_1329 =
               match uu___90_1329 with
               | FStar_Parser_AST.DefineEffect (uu____1330,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____1344,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___91_1355 =
               match uu___91_1355 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____1356,t);
                   FStar_Parser_AST.brange = uu____1358;
                   FStar_Parser_AST.blevel = uu____1359;
                   FStar_Parser_AST.aqual = uu____1360;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____1361,t);
                   FStar_Parser_AST.brange = uu____1363;
                   FStar_Parser_AST.blevel = uu____1364;
                   FStar_Parser_AST.aqual = uu____1365;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____1367;
                   FStar_Parser_AST.blevel = uu____1368;
                   FStar_Parser_AST.aqual = uu____1369;_} -> collect_term t
               | uu____1370 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___92_1372 =
               match uu___92_1372 with
               | FStar_Const.Const_int
                   (uu____1373,FStar_Pervasives_Native.Some
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
                   let uu____1388 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____1388
               | uu____1389 -> ()
             and collect_term' uu___93_1390 =
               match uu___93_1390 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____1399 =
                         let uu____1400 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____1400 in
                       collect_term' uu____1399)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____1402 -> ()
               | FStar_Parser_AST.Uvar uu____1403 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____1406) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____1433  ->
                         match uu____1433 with
                         | (t,uu____1439) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____1449) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____1451,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____1471  ->
                         match uu____1471 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____1482,t1,t2) ->
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
                      (fun uu____1575  ->
                         match uu____1575 with
                         | (uu____1580,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____1583) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____1639,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____1642,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____1645) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____1651) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____1657,uu____1658) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___94_1666 =
               match uu___94_1666 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____1667 -> ()
               | FStar_Parser_AST.PatConst uu____1668 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____1676 -> ()
               | FStar_Parser_AST.PatName uu____1683 -> ()
               | FStar_Parser_AST.PatTvar uu____1684 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____1698) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____1714  ->
                        match uu____1714 with
                        | (uu____1719,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____1743 =
               match uu____1743 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____1761 = FStar_Parser_Driver.parse_file filename in
             match uu____1761 with
             | (ast,uu____1775) -> (collect_file ast; FStar_ST.read deps))
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let uu____1819 =
     let uu____1820 =
       let uu____1821 =
         let uu____1822 =
           let uu____1825 =
             let uu____1828 = FStar_Util.smap_keys graph in
             FStar_List.unique uu____1828 in
           FStar_List.collect
             (fun k  ->
                let deps =
                  let uu____1841 =
                    let uu____1848 = FStar_Util.smap_try_find graph k in
                    FStar_Util.must uu____1848 in
                  FStar_Pervasives_Native.fst uu____1841 in
                let r s = FStar_Util.replace_char s '.' '_' in
                FStar_List.map
                  (fun dep1  ->
                     FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
             uu____1825 in
         FStar_String.concat "\n" uu____1822 in
       Prims.strcat uu____1821 "\n}\n" in
     Prims.strcat "digraph {\n" uu____1820 in
   FStar_Util.write_file "dep.graph" uu____1819)
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
        let uu____1958 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____1968 = FStar_Util.mk_ref false in (f, uu____1968))
          uu____1958 in
      let partial_discovery =
        let uu____1976 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____1976 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____1982 =
          let uu____1991 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____1991 in
        match uu____1982 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____2047) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____2079 =
          let uu____2080 = FStar_Util.smap_try_find graph key in
          uu____2080 = FStar_Pervasives_Native.None in
        if uu____2079
        then
          let uu____2109 =
            let uu____2118 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____2118 in
          match uu____2109 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____2171) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____2177) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____2184) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____2210 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____2212 = lowercase_module_name f1 in
                     uu____2212 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____2210) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____2249 =
           let uu____2256 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____2256 in
         match uu____2249 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1
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
                      let uu____2312 =
                        let uu____2315 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____2323 = discover (key :: cycle) dep1 in
                               dep1 :: uu____2323) direct_deps in
                        FStar_List.flatten uu____2315 in
                      FStar_List.unique uu____2312 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____2336 =
                       let uu____2339 = FStar_ST.read topologically_sorted in
                       key :: uu____2339 in
                     FStar_ST.write topologically_sorted uu____2336);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____2361 =
           let uu____2370 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____2370 in
         match uu____2361 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____2405 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____2407 = lowercase_module_name f in
                       uu____2407 = k) filenames in
                Prims.op_Negation uu____2405)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____2415 = lowercase_module_name f in
                     uu____2415 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____2417) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____2439 = must_find f in FStar_List.rev uu____2439 in
       let by_target =
         let uu____2451 =
           let uu____2454 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____2454 in
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
                     let uu____2488 =
                       let uu____2497 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____2497 in
                     match uu____2488 with
                     | (FStar_Pervasives_Native.Some intf,uu____2527) when
                         should_append_fsti -> [intf]
                     | uu____2534 -> [] in
                   let deps =
                     let uu____2546 = discover1 k1 in
                     FStar_List.rev uu____2546 in
                   let deps_as_filenames =
                     let uu____2552 = FStar_List.collect must_find deps in
                     FStar_List.append uu____2552 suffix in
                   (f, deps_as_filenames)) as_list) uu____2451 in
       let topologically_sorted1 =
         let uu____2560 = FStar_ST.read topologically_sorted in
         FStar_List.collect must_find_r uu____2560 in
       FStar_List.iter
         (fun uu____2574  ->
            match uu____2574 with
            | (m1,r) ->
                let uu____2587 =
                  (let uu____2588 = FStar_ST.read r in
                   Prims.op_Negation uu____2588) &&
                    (let uu____2591 = FStar_Options.interactive () in
                     Prims.op_Negation uu____2591) in
                if uu____2587
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____2594 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____2598 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____2598 = ".fst") in
                    if uu____2594
                    then
                      let uu____2602 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____2602
                    else "" in
                  let uu____2607 =
                    let uu____2608 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____2608 in
                  raise uu____2607
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____2653  ->
         match uu____2653 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print uu____2700 =
  match uu____2700 with
  | (make_deps,uu____2724,graph) ->
      let uu____2758 = FStar_Options.dep () in
      (match uu____2758 with
       | FStar_Pervasives_Native.Some "make" -> print_make make_deps
       | FStar_Pervasives_Native.Some "graph" -> print_graph graph
       | FStar_Pervasives_Native.Some uu____2761 ->
           raise (FStar_Errors.Err "unknown tool for --dep\n")
       | FStar_Pervasives_Native.None  -> ())