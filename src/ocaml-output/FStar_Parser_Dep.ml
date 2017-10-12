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
  fun f  -> let uu____155 = is_interface f in Prims.op_Negation uu____155
let list_of_option:
  'Auu____160 .
    'Auu____160 FStar_Pervasives_Native.option -> 'Auu____160 Prims.list
  =
  fun uu___82_168  ->
    match uu___82_168 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____176 .
    ('Auu____176 FStar_Pervasives_Native.option,'Auu____176
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____176 Prims.list
  =
  fun uu____190  ->
    match uu____190 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____213 =
      let uu____216 = FStar_Util.basename f in
      check_and_strip_suffix uu____216 in
    match uu____213 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____218 =
          let uu____219 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____219 in
        FStar_Exn.raise uu____218
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____229  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____246 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____246 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____272 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____272
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____293 =
              let uu____294 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____294 in
            FStar_Exn.raise uu____293)) include_directories2
let build_map: Prims.string Prims.list -> map =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____335 = FStar_Util.smap_try_find map1 key in
      match uu____335 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____372 = is_interface full_path in
          if uu____372
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____406 = is_interface full_path in
          if uu____406
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____433 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____447  ->
          match uu____447 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____433);
    FStar_List.iter
      (fun f  ->
         let uu____458 = lowercase_module_name f in add_entry uu____458 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____476 =
           let uu____479 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____479 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____505 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____505 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____476);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____679 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____679 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____692 = string_of_lid l last1 in
      FStar_String.lowercase uu____692
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____697 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____697
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____709 =
        let uu____710 =
          let uu____711 =
            let uu____712 =
              let uu____715 = FStar_Util.basename filename in
              check_and_strip_suffix uu____715 in
            FStar_Util.must uu____712 in
          FStar_String.lowercase uu____711 in
        uu____710 <> k' in
      if uu____709
      then
        let uu____716 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____716 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____722 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____737 = FStar_Options.prims_basename () in
      let uu____738 =
        let uu____741 = FStar_Options.pervasives_basename () in
        let uu____742 =
          let uu____745 = FStar_Options.pervasives_native_basename () in
          [uu____745] in
        uu____741 :: uu____742 in
      uu____737 :: uu____738 in
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
              let uu____824 =
                let uu____825 =
                  let uu____826 = FStar_ST.op_Bang deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____826 in
                Prims.op_Negation uu____825 in
              if uu____824
              then
                let uu____895 =
                  let uu____898 = FStar_ST.op_Bang deps in d :: uu____898 in
                FStar_ST.op_Colon_Equals deps uu____895
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____1057 = FStar_Util.smap_try_find working_map key in
              match uu____1057 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____1097 = lowercase_module_name f in
                        add_dep uu____1097) (list_of_pair pair);
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
                        (let uu____1109 = string_of_lid lid true in
                         FStar_Util.print2_warning
                           "Warning: in %s: no modules in namespace %s and no file with that name either\n"
                           filename uu____1109))
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
                    let uu____1125 = string_of_lid lid true in
                    FStar_Util.print1_warning
                      "Warning: no modules in namespace %s and no file with that name either\n"
                      uu____1125
              else () in
            let record_open let_open lid =
              let uu____1134 = record_open_module let_open lid in
              if uu____1134
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____1149 =
              match uu____1149 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____1156 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____1166 = FStar_Util.smap_try_find original_map alias in
              match uu____1166 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____1218 =
                    let uu____1219 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____1219 in
                  FStar_Exn.raise uu____1218 in
            let record_lid lid =
              let try_key key =
                let uu____1228 = FStar_Util.smap_try_find working_map key in
                match uu____1228 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____1267 = lowercase_module_name f in
                         add_dep uu____1267) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____1276 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____1276
                    then
                      let uu____1277 =
                        let uu____1278 = string_of_lid lid false in
                        FStar_Util.format1 "Unbound module reference %s"
                          uu____1278 in
                      FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                        uu____1277
                    else () in
              let uu____1281 = lowercase_join_longident lid false in
              try_key uu____1281 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_module uu___83_1366 =
               match uu___83_1366 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1375 =
                         let uu____1376 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1376 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1379 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1379
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1380 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1380
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1484  ->
                              match uu____1484 with
                              | (m,r) ->
                                  let uu____1773 =
                                    let uu____1774 =
                                      let uu____1775 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1775 in
                                    (FStar_String.lowercase m) = uu____1774 in
                                  if uu____1773
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____1921) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1928 =
                         let uu____1929 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1929 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1932 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1932
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1933 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1933
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____2037  ->
                              match uu____2037 with
                              | (m,r) ->
                                  let uu____2326 =
                                    let uu____2327 =
                                      let uu____2328 = string_of_lid lid true in
                                      FStar_String.lowercase uu____2328 in
                                    (FStar_String.lowercase m) = uu____2327 in
                                  if uu____2326
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___84_2479 =
               match uu___84_2479 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____2485 = lowercase_join_longident lid true in
                     add_dep uu____2485);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____2486,patterms) ->
                   FStar_List.iter
                     (fun uu____2508  ->
                        match uu____2508 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____2517,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2519;
                     FStar_Parser_AST.mdest = uu____2520;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2522;
                     FStar_Parser_AST.mdest = uu____2523;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____2525,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2527;
                     FStar_Parser_AST.mdest = uu____2528;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____2532,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____2562  ->
                          match uu____2562 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____2575,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____2582 -> ()
               | FStar_Parser_AST.Pragma uu____2583 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____2607 =
                       let uu____2608 = FStar_ST.op_Bang num_of_toplevelmods in
                       uu____2608 > (Prims.parse_int "1") in
                     if uu____2607
                     then
                       let uu____2669 =
                         let uu____2670 =
                           let uu____2671 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____2671 in
                         FStar_Errors.Err uu____2670 in
                       FStar_Exn.raise uu____2669
                     else ()))
             and collect_tycon uu___85_2673 =
               match uu___85_2673 with
               | FStar_Parser_AST.TyconAbstract (uu____2674,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____2686,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____2700,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2746  ->
                         match uu____2746 with
                         | (uu____2755,t,uu____2757) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____2762,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2821  ->
                         match uu____2821 with
                         | (uu____2834,t,uu____2836,uu____2837) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___86_2846 =
               match uu___86_2846 with
               | FStar_Parser_AST.DefineEffect (uu____2847,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____2861,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___87_2872 =
               match uu___87_2872 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____2873,t);
                   FStar_Parser_AST.brange = uu____2875;
                   FStar_Parser_AST.blevel = uu____2876;
                   FStar_Parser_AST.aqual = uu____2877;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____2878,t);
                   FStar_Parser_AST.brange = uu____2880;
                   FStar_Parser_AST.blevel = uu____2881;
                   FStar_Parser_AST.aqual = uu____2882;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____2884;
                   FStar_Parser_AST.blevel = uu____2885;
                   FStar_Parser_AST.aqual = uu____2886;_} -> collect_term t
               | uu____2887 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___88_2889 =
               match uu___88_2889 with
               | FStar_Const.Const_int
                   (uu____2890,FStar_Pervasives_Native.Some
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
                   let uu____2905 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____2905
               | FStar_Const.Const_char uu____2906 -> add_dep "fstar.char"
               | FStar_Const.Const_float uu____2907 -> add_dep "fstar.float"
               | uu____2908 -> ()
             and collect_term' uu___89_2909 =
               match uu___89_2909 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____2918 =
                         let uu____2919 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____2919 in
                       collect_term' uu____2918)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____2921 -> ()
               | FStar_Parser_AST.Uvar uu____2922 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____2925) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____2955  ->
                         match uu____2955 with
                         | (t,uu____2961) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____2971) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____2973,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____2997  ->
                         match uu____2997 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____3008,t1,t2) ->
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
                      (fun uu____3104  ->
                         match uu____3104 with
                         | (uu____3109,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____3112) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____3168,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____3171,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____3174) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____3180) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____3186,uu____3187) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___90_3195 =
               match uu___90_3195 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____3196 -> ()
               | FStar_Parser_AST.PatConst uu____3197 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____3205 -> ()
               | FStar_Parser_AST.PatName uu____3212 -> ()
               | FStar_Parser_AST.PatTvar uu____3213 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____3227) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____3246  ->
                        match uu____3246 with
                        | (uu____3251,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____3275 =
               match uu____3275 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____3293 = FStar_Parser_Driver.parse_file filename in
             match uu____3293 with
             | (ast,uu____3307) ->
                 (collect_module ast; FStar_ST.op_Bang deps))
let print_graph:
  'Auu____3389 .
    (Prims.string Prims.list,'Auu____3389) FStar_Pervasives_Native.tuple2
      FStar_Util.smap -> Prims.unit
  =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____3413 =
       let uu____3414 =
         let uu____3415 =
           let uu____3416 =
             let uu____3419 =
               let uu____3422 = FStar_Util.smap_keys graph in
               FStar_List.unique uu____3422 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____3438 =
                      let uu____3445 = FStar_Util.smap_try_find graph k in
                      FStar_Util.must uu____3445 in
                    FStar_Pervasives_Native.fst uu____3438 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  FStar_List.map
                    (fun dep1  ->
                       FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
               uu____3419 in
           FStar_String.concat "\n" uu____3416 in
         Prims.strcat uu____3415 "\n}\n" in
       Prims.strcat "digraph {\n" uu____3414 in
     FStar_Util.write_file "dep.graph" uu____3413)
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
        let uu____3534 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____3546 = FStar_Util.mk_ref false in (f, uu____3546))
          uu____3534 in
      let partial_discovery =
        let uu____3566 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____3566 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____3572 =
          let uu____3581 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____3581 in
        match uu____3572 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____3637) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____3669 =
          let uu____3670 = FStar_Util.smap_try_find graph key in
          uu____3670 = FStar_Pervasives_Native.None in
        if uu____3669
        then
          let uu____3699 =
            let uu____3708 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____3708 in
          match uu____3699 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____3761) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____3767) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____3774) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____3801 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____3806 = lowercase_module_name f1 in
                     uu____3806 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____3801) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____3843 =
           let uu____3850 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____3850 in
         match uu____3843 with
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
                      let uu____3906 =
                        let uu____3909 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____3919 = discover (key :: cycle) dep1 in
                               dep1 :: uu____3919) direct_deps in
                        FStar_List.flatten uu____3909 in
                      FStar_List.unique uu____3906 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____3932 =
                       let uu____3935 = FStar_ST.op_Bang topologically_sorted in
                       key :: uu____3935 in
                     FStar_ST.op_Colon_Equals topologically_sorted uu____3932);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____4077 =
           let uu____4086 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____4086 in
         match uu____4077 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____4122 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____4126 = lowercase_module_name f in
                       uu____4126 = k) filenames in
                Prims.op_Negation uu____4122)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____4136 = lowercase_module_name f in
                     uu____4136 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____4138) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____4160 = must_find f in FStar_List.rev uu____4160 in
       let by_target =
         let uu____4172 =
           let uu____4175 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____4175 in
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
                     let uu____4220 =
                       let uu____4229 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____4229 in
                     match uu____4220 with
                     | (FStar_Pervasives_Native.Some intf,uu____4259) when
                         should_append_fsti -> [intf]
                     | uu____4266 -> [] in
                   let deps =
                     let uu____4278 = discover1 k1 in
                     FStar_List.rev uu____4278 in
                   let deps_as_filenames =
                     let uu____4284 = FStar_List.collect must_find deps in
                     FStar_List.append uu____4284 suffix in
                   (f, deps_as_filenames)) as_list) uu____4172 in
       let topologically_sorted1 =
         let uu____4292 = FStar_ST.op_Bang topologically_sorted in
         FStar_List.collect must_find_r uu____4292 in
       FStar_List.iter
         (fun uu____4464  ->
            match uu____4464 with
            | (m1,r) ->
                let uu____4753 =
                  (let uu____4756 = FStar_ST.op_Bang r in
                   Prims.op_Negation uu____4756) &&
                    (let uu____4900 = FStar_Options.interactive () in
                     Prims.op_Negation uu____4900) in
                if uu____4753
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____4903 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____4911 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____4911 = ".fst") in
                    if uu____4903
                    then
                      let uu____4918 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____4918
                    else "" in
                  let uu____4926 =
                    let uu____4927 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____4927 in
                  FStar_Exn.raise uu____4926
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____4977  ->
         match uu____4977 with
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
  fun uu____5028  ->
    match uu____5028 with
    | (make_deps,uu____5052,graph) ->
        let uu____5086 = FStar_Options.dep () in
        (match uu____5086 with
         | FStar_Pervasives_Native.Some "make" -> print_make make_deps
         | FStar_Pervasives_Native.Some "graph" -> print_graph graph
         | FStar_Pervasives_Native.Some uu____5089 ->
             FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
         | FStar_Pervasives_Native.None  -> ())