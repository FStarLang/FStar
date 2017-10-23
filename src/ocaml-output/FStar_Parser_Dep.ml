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
  fun uu___90_162  ->
    match uu___90_162 with
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
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____223  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____240 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____240 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____266 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____266
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____287 =
              let uu____288 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____288 in
            FStar_Exn.raise uu____287)) include_directories2
let build_map: Prims.string Prims.list -> map =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____329 = FStar_Util.smap_try_find map1 key in
      match uu____329 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____366 = is_interface full_path in
          if uu____366
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____400 = is_interface full_path in
          if uu____400
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____427 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____441  ->
          match uu____441 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____427);
    FStar_List.iter
      (fun f  ->
         let uu____452 = lowercase_module_name f in add_entry uu____452 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____470 =
           let uu____473 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____473 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____499 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____499 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____470);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____673 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____673 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____686 = string_of_lid l last1 in
      FStar_String.lowercase uu____686
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____691 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____691
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____703 =
        let uu____704 =
          let uu____705 =
            let uu____706 =
              let uu____709 = FStar_Util.basename filename in
              check_and_strip_suffix uu____709 in
            FStar_Util.must uu____706 in
          FStar_String.lowercase uu____705 in
        uu____704 <> k' in
      if uu____703
      then
        let uu____710 =
          let uu____711 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
            uu____711 filename in
        FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____710
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____717 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____732 = FStar_Options.prims_basename () in
      let uu____733 =
        let uu____736 = FStar_Options.pervasives_basename () in
        let uu____737 =
          let uu____740 = FStar_Options.pervasives_native_basename () in
          [uu____740] in
        uu____736 :: uu____737 in
      uu____732 :: uu____733 in
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
              let uu____819 =
                let uu____820 =
                  let uu____821 = FStar_ST.op_Bang deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____821 in
                Prims.op_Negation uu____820 in
              if uu____819
              then
                let uu____890 =
                  let uu____893 = FStar_ST.op_Bang deps in d :: uu____893 in
                FStar_ST.op_Colon_Equals deps uu____890
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____1052 = FStar_Util.smap_try_find working_map key in
              match uu____1052 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____1092 = lowercase_module_name f in
                        add_dep uu____1092) (list_of_pair pair);
                   true)
              | FStar_Pervasives_Native.None  ->
                  let r = enter_namespace original_map working_map key in
                  (if Prims.op_Negation r
                   then
                     (if let_open
                      then
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("let-open only supported for modules, not namespaces",
                               (FStar_Ident.range_of_lid lid)))
                      else
                        (let uu____1104 =
                           let uu____1105 = string_of_lid lid true in
                           FStar_Util.format1
                             "No modules in namespace %s and no file with that name either"
                             uu____1105 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                           uu____1104))
                   else ();
                   false) in
            let record_open_namespace error_msg lid =
              let key = lowercase_join_longident lid true in
              let r = enter_namespace original_map working_map key in
              if Prims.op_Negation r
              then
                match error_msg with
                | FStar_Pervasives_Native.Some e ->
                    FStar_Exn.raise
                      (FStar_Errors.Error (e, (FStar_Ident.range_of_lid lid)))
                | FStar_Pervasives_Native.None  ->
                    let uu____1121 =
                      let uu____1122 = string_of_lid lid true in
                      FStar_Util.format1
                        "No modules in namespace %s and no file with that name either"
                        uu____1122 in
                    FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                      uu____1121
              else () in
            let record_open let_open lid =
              let uu____1131 = record_open_module let_open lid in
              if uu____1131
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____1146 =
              match uu____1146 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____1153 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____1163 = FStar_Util.smap_try_find original_map alias in
              match uu____1163 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____1215 =
                    let uu____1216 =
                      let uu____1221 =
                        FStar_Util.format1
                          "module not found in search path: %s\n" alias in
                      (uu____1221, (FStar_Ident.range_of_lid lid)) in
                    FStar_Errors.Error uu____1216 in
                  FStar_Exn.raise uu____1215 in
            let record_lid lid =
              let try_key key =
                let uu____1230 = FStar_Util.smap_try_find working_map key in
                match uu____1230 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____1269 = lowercase_module_name f in
                         add_dep uu____1269) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____1278 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____1278
                    then
                      let uu____1279 =
                        let uu____1280 = string_of_lid lid false in
                        FStar_Util.format1 "Unbound module reference %s"
                          uu____1280 in
                      FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                        uu____1279
                    else () in
              let uu____1283 = lowercase_join_longident lid false in
              try_key uu____1283 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_module uu___91_1368 =
               match uu___91_1368 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1377 =
                         let uu____1378 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1378 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1381 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1381
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1382 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1382
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1486  ->
                              match uu____1486 with
                              | (m,r) ->
                                  let uu____1775 =
                                    let uu____1776 =
                                      let uu____1777 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1777 in
                                    (FStar_String.lowercase m) = uu____1776 in
                                  if uu____1775
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____1923) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1930 =
                         let uu____1931 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1931 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1934 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1934
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1935 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1935
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____2039  ->
                              match uu____2039 with
                              | (m,r) ->
                                  let uu____2328 =
                                    let uu____2329 =
                                      let uu____2330 = string_of_lid lid true in
                                      FStar_String.lowercase uu____2330 in
                                    (FStar_String.lowercase m) = uu____2329 in
                                  if uu____2328
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___92_2481 =
               match uu___92_2481 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____2487 = lowercase_join_longident lid true in
                     add_dep uu____2487);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____2488,patterms) ->
                   FStar_List.iter
                     (fun uu____2510  ->
                        match uu____2510 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____2519,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2521;
                     FStar_Parser_AST.mdest = uu____2522;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2524;
                     FStar_Parser_AST.mdest = uu____2525;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____2527,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2529;
                     FStar_Parser_AST.mdest = uu____2530;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____2534,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____2564  ->
                          match uu____2564 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____2577,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____2584 -> ()
               | FStar_Parser_AST.Pragma uu____2585 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____2609 =
                       let uu____2610 = FStar_ST.op_Bang num_of_toplevelmods in
                       uu____2610 > (Prims.parse_int "1") in
                     if uu____2609
                     then
                       let uu____2671 =
                         let uu____2672 =
                           let uu____2677 =
                             let uu____2678 = string_of_lid lid true in
                             FStar_Util.format1
                               "Automatic dependency analysis demands one module per file (module %s not supported)"
                               uu____2678 in
                           (uu____2677, (FStar_Ident.range_of_lid lid)) in
                         FStar_Errors.Error uu____2672 in
                       FStar_Exn.raise uu____2671
                     else ()))
             and collect_tycon uu___93_2680 =
               match uu___93_2680 with
               | FStar_Parser_AST.TyconAbstract (uu____2681,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____2693,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____2707,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2753  ->
                         match uu____2753 with
                         | (uu____2762,t,uu____2764) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____2769,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2828  ->
                         match uu____2828 with
                         | (uu____2841,t,uu____2843,uu____2844) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___94_2853 =
               match uu___94_2853 with
               | FStar_Parser_AST.DefineEffect (uu____2854,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____2868,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___95_2879 =
               match uu___95_2879 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____2880,t);
                   FStar_Parser_AST.brange = uu____2882;
                   FStar_Parser_AST.blevel = uu____2883;
                   FStar_Parser_AST.aqual = uu____2884;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____2885,t);
                   FStar_Parser_AST.brange = uu____2887;
                   FStar_Parser_AST.blevel = uu____2888;
                   FStar_Parser_AST.aqual = uu____2889;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____2891;
                   FStar_Parser_AST.blevel = uu____2892;
                   FStar_Parser_AST.aqual = uu____2893;_} -> collect_term t
               | uu____2894 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___96_2896 =
               match uu___96_2896 with
               | FStar_Const.Const_int
                   (uu____2897,FStar_Pervasives_Native.Some
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
                   let uu____2912 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____2912
               | FStar_Const.Const_char uu____2913 -> add_dep "fstar.char"
               | FStar_Const.Const_float uu____2914 -> add_dep "fstar.float"
               | uu____2915 -> ()
             and collect_term' uu___97_2916 =
               match uu___97_2916 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____2925 =
                         let uu____2926 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____2926 in
                       collect_term' uu____2925)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____2928 -> ()
               | FStar_Parser_AST.Uvar uu____2929 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____2932) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____2962  ->
                         match uu____2962 with
                         | (t,uu____2968) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____2978) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____2980,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____3004  ->
                         match uu____3004 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____3015,t1,t2) ->
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
                      (fun uu____3111  ->
                         match uu____3111 with
                         | (uu____3116,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____3119) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____3175,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____3178,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____3181) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____3187) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____3193,uu____3194) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___98_3202 =
               match uu___98_3202 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____3203 -> ()
               | FStar_Parser_AST.PatConst uu____3204 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____3212 -> ()
               | FStar_Parser_AST.PatName uu____3219 -> ()
               | FStar_Parser_AST.PatTvar uu____3220 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____3234) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____3253  ->
                        match uu____3253 with
                        | (uu____3258,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____3282 =
               match uu____3282 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____3300 = FStar_Parser_Driver.parse_file filename in
             match uu____3300 with
             | (ast,uu____3314) ->
                 (collect_module ast; FStar_ST.op_Bang deps))
let print_graph:
  'Auu____3396 .
    (Prims.string Prims.list,'Auu____3396) FStar_Pervasives_Native.tuple2
      FStar_Util.smap -> Prims.unit
  =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____3420 =
       let uu____3421 =
         let uu____3422 =
           let uu____3423 =
             let uu____3426 =
               let uu____3429 = FStar_Util.smap_keys graph in
               FStar_List.unique uu____3429 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____3445 =
                      let uu____3452 = FStar_Util.smap_try_find graph k in
                      FStar_Util.must uu____3452 in
                    FStar_Pervasives_Native.fst uu____3445 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  FStar_List.map
                    (fun dep1  ->
                       FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
               uu____3426 in
           FStar_String.concat "\n" uu____3423 in
         Prims.strcat uu____3422 "\n}\n" in
       Prims.strcat "digraph {\n" uu____3421 in
     FStar_Util.write_file "dep.graph" uu____3420)
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
        let uu____3541 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____3553 = FStar_Util.mk_ref false in (f, uu____3553))
          uu____3541 in
      let partial_discovery =
        let uu____3573 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____3573 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____3579 =
          let uu____3588 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____3588 in
        match uu____3579 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____3644) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____3676 =
          let uu____3677 = FStar_Util.smap_try_find graph key in
          uu____3677 = FStar_Pervasives_Native.None in
        if uu____3676
        then
          let uu____3706 =
            let uu____3715 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____3715 in
          match uu____3706 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____3768) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____3774) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____3781) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____3808 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____3813 = lowercase_module_name f1 in
                     uu____3813 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____3808) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____3850 =
           let uu____3857 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____3857 in
         match uu____3850 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1_warning
                     "Recursive dependency on module %s\n" key;
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
                      let uu____3913 =
                        let uu____3916 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____3926 = discover (key :: cycle) dep1 in
                               dep1 :: uu____3926) direct_deps in
                        FStar_List.flatten uu____3916 in
                      FStar_List.unique uu____3913 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____3939 =
                       let uu____3942 = FStar_ST.op_Bang topologically_sorted in
                       key :: uu____3942 in
                     FStar_ST.op_Colon_Equals topologically_sorted uu____3939);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____4084 =
           let uu____4093 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____4093 in
         match uu____4084 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____4129 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____4133 = lowercase_module_name f in
                       uu____4133 = k) filenames in
                Prims.op_Negation uu____4129)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____4143 = lowercase_module_name f in
                     uu____4143 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____4145) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____4167 = must_find f in FStar_List.rev uu____4167 in
       let by_target =
         let uu____4179 =
           let uu____4182 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____4182 in
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
                     let uu____4227 =
                       let uu____4236 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____4236 in
                     match uu____4227 with
                     | (FStar_Pervasives_Native.Some intf,uu____4266) when
                         should_append_fsti -> [intf]
                     | uu____4273 -> [] in
                   let deps =
                     let uu____4285 = discover1 k1 in
                     FStar_List.rev uu____4285 in
                   let deps_as_filenames =
                     let uu____4291 = FStar_List.collect must_find deps in
                     FStar_List.append uu____4291 suffix in
                   (f, deps_as_filenames)) as_list) uu____4179 in
       let topologically_sorted1 =
         let uu____4299 = FStar_ST.op_Bang topologically_sorted in
         FStar_List.collect must_find_r uu____4299 in
       FStar_List.iter
         (fun uu____4471  ->
            match uu____4471 with
            | (m1,r) ->
                let uu____4760 =
                  (let uu____4763 = FStar_ST.op_Bang r in
                   Prims.op_Negation uu____4763) &&
                    (let uu____4907 = FStar_Options.interactive () in
                     Prims.op_Negation uu____4907) in
                if uu____4760
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____4910 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____4918 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____4918 = ".fst") in
                    if uu____4910
                    then
                      let uu____4925 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____4925
                    else "" in
                  let uu____4933 =
                    let uu____4934 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____4934 in
                  FStar_Exn.raise uu____4933
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____4984  ->
         match uu____4984 with
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
  fun uu____5035  ->
    match uu____5035 with
    | (make_deps,uu____5059,graph) ->
        let uu____5093 = FStar_Options.dep () in
        (match uu____5093 with
         | FStar_Pervasives_Native.Some "make" -> print_make make_deps
         | FStar_Pervasives_Native.Some "graph" -> print_graph graph
         | FStar_Pervasives_Native.Some uu____5096 ->
             FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
         | FStar_Pervasives_Native.None  -> ())