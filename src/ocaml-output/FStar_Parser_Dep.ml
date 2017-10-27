open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut[@@deriving show]
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
    FStar_Pervasives_Native.tuple2 FStar_Util.smap[@@deriving show]
type color =
  | White
  | Gray
  | Black[@@deriving show]
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____26 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____30 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____34 -> false
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
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
           let uu____68 =
             (l > lext) &&
               (let uu____80 = FStar_String.substring f (l - lext) lext in
                uu____80 = ext) in
           if uu____68
           then
             let uu____97 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____97
           else FStar_Pervasives_Native.None) suffixes in
    let uu____109 = FStar_List.filter FStar_Util.is_some matches in
    match uu____109 with
    | (FStar_Pervasives_Native.Some m)::uu____119 ->
        FStar_Pervasives_Native.Some m
    | uu____126 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____134 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____134 = 105
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____138 = is_interface f in Prims.op_Negation uu____138
let list_of_option:
  'Auu____141 .
    'Auu____141 FStar_Pervasives_Native.option -> 'Auu____141 Prims.list
  =
  fun uu___90_149  ->
    match uu___90_149 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____155 .
    ('Auu____155 FStar_Pervasives_Native.option,'Auu____155
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____155 Prims.list
  =
  fun uu____169  ->
    match uu____169 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____191 =
      let uu____194 = FStar_Util.basename f in
      check_and_strip_suffix uu____194 in
    match uu____191 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____196 =
          let uu____197 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____197 in
        FStar_Exn.raise uu____196
let build_inclusion_candidates_list:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____206  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____223 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____223 in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____249 = check_and_strip_suffix f1 in
                FStar_All.pipe_right uu____249
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1 in
                        (longname, full_path)))) files
         else
           (let uu____270 =
              let uu____271 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____271 in
            FStar_Exn.raise uu____270)) include_directories2
let build_map: Prims.string Prims.list -> map =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____311 = FStar_Util.smap_try_find map1 key in
      match uu____311 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____348 = is_interface full_path in
          if uu____348
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____382 = is_interface full_path in
          if uu____382
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    (let uu____409 = build_inclusion_candidates_list () in
     FStar_List.iter
       (fun uu____423  ->
          match uu____423 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____409);
    FStar_List.iter
      (fun f  ->
         let uu____434 = lowercase_module_name f in add_entry uu____434 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____449 =
           let uu____452 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____452 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____478 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____478 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____449);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____650 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____650 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____661 = string_of_lid l last1 in
      FStar_String.lowercase uu____661
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____665 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____665
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____675 =
        let uu____676 =
          let uu____677 =
            let uu____678 =
              let uu____681 = FStar_Util.basename filename in
              check_and_strip_suffix uu____681 in
            FStar_Util.must uu____678 in
          FStar_String.lowercase uu____677 in
        uu____676 <> k' in
      if uu____675
      then
        let uu____682 =
          let uu____683 = string_of_lid lid true in
          FStar_Util.format2
            "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
            uu____683 filename in
        FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____682
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____688 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____702 = FStar_Options.prims_basename () in
      let uu____703 =
        let uu____706 = FStar_Options.pervasives_basename () in
        let uu____707 =
          let uu____710 = FStar_Options.pervasives_native_basename () in
          [uu____710] in
        uu____706 :: uu____707 in
      uu____702 :: uu____703 in
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
              let uu____784 =
                let uu____785 =
                  let uu____786 = FStar_ST.op_Bang deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____786 in
                Prims.op_Negation uu____785 in
              if uu____784
              then
                let uu____855 =
                  let uu____858 = FStar_ST.op_Bang deps in d :: uu____858 in
                FStar_ST.op_Colon_Equals deps uu____855
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____1017 = FStar_Util.smap_try_find working_map key in
              match uu____1017 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____1057 = lowercase_module_name f in
                        add_dep uu____1057) (list_of_pair pair);
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
                        (let uu____1069 =
                           let uu____1070 = string_of_lid lid true in
                           FStar_Util.format1
                             "No modules in namespace %s and no file with that name either"
                             uu____1070 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                           uu____1069))
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
                    let uu____1086 =
                      let uu____1087 = string_of_lid lid true in
                      FStar_Util.format1
                        "No modules in namespace %s and no file with that name either"
                        uu____1087 in
                    FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                      uu____1086
              else () in
            let record_open let_open lid =
              let uu____1096 = record_open_module let_open lid in
              if uu____1096
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____1111 =
              match uu____1111 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____1118 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____1128 = FStar_Util.smap_try_find original_map alias in
              match uu____1128 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____1180 =
                    let uu____1181 =
                      let uu____1186 =
                        FStar_Util.format1
                          "module not found in search path: %s\n" alias in
                      (uu____1186, (FStar_Ident.range_of_lid lid)) in
                    FStar_Errors.Error uu____1181 in
                  FStar_Exn.raise uu____1180 in
            let record_lid lid =
              let try_key key =
                let uu____1195 = FStar_Util.smap_try_find working_map key in
                match uu____1195 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____1234 = lowercase_module_name f in
                         add_dep uu____1234) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____1243 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____1243
                    then
                      let uu____1244 =
                        let uu____1245 = string_of_lid lid false in
                        FStar_Util.format1 "Unbound module reference %s"
                          uu____1245 in
                      FStar_Errors.warn (FStar_Ident.range_of_lid lid)
                        uu____1244
                    else () in
              let uu____1248 = lowercase_join_longident lid false in
              try_key uu____1248 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_module uu___91_1333 =
               match uu___91_1333 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1342 =
                         let uu____1343 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1343 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1346 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1346
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1347 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1347
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1451  ->
                              match uu____1451 with
                              | (m,r) ->
                                  let uu____1740 =
                                    let uu____1741 =
                                      let uu____1742 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1742 in
                                    (FStar_String.lowercase m) = uu____1741 in
                                  if uu____1740
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____1888) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1895 =
                         let uu____1896 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1896 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1899 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1899
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1900 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1900
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____2004  ->
                              match uu____2004 with
                              | (m,r) ->
                                  let uu____2293 =
                                    let uu____2294 =
                                      let uu____2295 = string_of_lid lid true in
                                      FStar_String.lowercase uu____2295 in
                                    (FStar_String.lowercase m) = uu____2294 in
                                  if uu____2293
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___92_2446 =
               match uu___92_2446 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____2452 = lowercase_join_longident lid true in
                     add_dep uu____2452);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____2453,patterms) ->
                   FStar_List.iter
                     (fun uu____2475  ->
                        match uu____2475 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____2484,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2486;
                     FStar_Parser_AST.mdest = uu____2487;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2489;
                     FStar_Parser_AST.mdest = uu____2490;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____2492,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____2494;
                     FStar_Parser_AST.mdest = uu____2495;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____2499,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____2529  ->
                          match uu____2529 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____2542,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____2549 -> ()
               | FStar_Parser_AST.Pragma uu____2550 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____2574 =
                       let uu____2575 = FStar_ST.op_Bang num_of_toplevelmods in
                       uu____2575 > (Prims.parse_int "1") in
                     if uu____2574
                     then
                       let uu____2636 =
                         let uu____2637 =
                           let uu____2642 =
                             let uu____2643 = string_of_lid lid true in
                             FStar_Util.format1
                               "Automatic dependency analysis demands one module per file (module %s not supported)"
                               uu____2643 in
                           (uu____2642, (FStar_Ident.range_of_lid lid)) in
                         FStar_Errors.Error uu____2637 in
                       FStar_Exn.raise uu____2636
                     else ()))
             and collect_tycon uu___93_2645 =
               match uu___93_2645 with
               | FStar_Parser_AST.TyconAbstract (uu____2646,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____2658,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____2672,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2718  ->
                         match uu____2718 with
                         | (uu____2727,t,uu____2729) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____2734,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2793  ->
                         match uu____2793 with
                         | (uu____2806,t,uu____2808,uu____2809) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___94_2818 =
               match uu___94_2818 with
               | FStar_Parser_AST.DefineEffect (uu____2819,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____2833,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___95_2844 =
               match uu___95_2844 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____2845,t);
                   FStar_Parser_AST.brange = uu____2847;
                   FStar_Parser_AST.blevel = uu____2848;
                   FStar_Parser_AST.aqual = uu____2849;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____2850,t);
                   FStar_Parser_AST.brange = uu____2852;
                   FStar_Parser_AST.blevel = uu____2853;
                   FStar_Parser_AST.aqual = uu____2854;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____2856;
                   FStar_Parser_AST.blevel = uu____2857;
                   FStar_Parser_AST.aqual = uu____2858;_} -> collect_term t
               | uu____2859 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___96_2861 =
               match uu___96_2861 with
               | FStar_Const.Const_int
                   (uu____2862,FStar_Pervasives_Native.Some
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
                   let uu____2877 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____2877
               | FStar_Const.Const_char uu____2878 -> add_dep "fstar.char"
               | FStar_Const.Const_float uu____2879 -> add_dep "fstar.float"
               | uu____2880 -> ()
             and collect_term' uu___97_2881 =
               match uu___97_2881 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____2890 =
                         let uu____2891 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____2891 in
                       collect_term' uu____2890)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____2893 -> ()
               | FStar_Parser_AST.Uvar uu____2894 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____2897) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____2927  ->
                         match uu____2927 with
                         | (t,uu____2933) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____2943) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____2945,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____2969  ->
                         match uu____2969 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____2980,t1,t2) ->
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
                      (fun uu____3076  ->
                         match uu____3076 with
                         | (uu____3081,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____3084) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____3140,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____3143,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____3146) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____3152) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____3158,uu____3159) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___98_3167 =
               match uu___98_3167 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____3168 -> ()
               | FStar_Parser_AST.PatConst uu____3169 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____3177 -> ()
               | FStar_Parser_AST.PatName uu____3184 -> ()
               | FStar_Parser_AST.PatTvar uu____3185 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____3199) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____3218  ->
                        match uu____3218 with
                        | (uu____3223,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____3247 =
               match uu____3247 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____3265 = FStar_Parser_Driver.parse_file filename in
             match uu____3265 with
             | (ast,uu____3279) ->
                 (collect_module ast; FStar_ST.op_Bang deps))
let print_graph:
  'Auu____3359 .
    (Prims.string Prims.list,'Auu____3359) FStar_Pervasives_Native.tuple2
      FStar_Util.smap -> Prims.unit
  =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____3383 =
       let uu____3384 =
         let uu____3385 =
           let uu____3386 =
             let uu____3389 =
               let uu____3392 = FStar_Util.smap_keys graph in
               FStar_List.unique uu____3392 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____3408 =
                      let uu____3415 = FStar_Util.smap_try_find graph k in
                      FStar_Util.must uu____3415 in
                    FStar_Pervasives_Native.fst uu____3408 in
                  let r s = FStar_Util.replace_char s 46 95 in
                  FStar_List.map
                    (fun dep1  ->
                       FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
               uu____3389 in
           FStar_String.concat "\n" uu____3386 in
         Prims.strcat uu____3385 "\n}\n" in
       Prims.strcat "digraph {\n" uu____3384 in
     FStar_Util.write_file "dep.graph" uu____3383)
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
        let uu____3502 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____3514 = FStar_Util.mk_ref false in (f, uu____3514))
          uu____3502 in
      let partial_discovery =
        let uu____3534 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____3534 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____3540 =
          let uu____3549 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____3549 in
        match uu____3540 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____3605) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____3637 =
          let uu____3638 = FStar_Util.smap_try_find graph key in
          uu____3638 = FStar_Pervasives_Native.None in
        if uu____3637
        then
          let uu____3667 =
            let uu____3676 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____3676 in
          match uu____3667 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____3729) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____3735) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____3742) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____3769 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____3774 = lowercase_module_name f1 in
                     uu____3774 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____3769) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____3811 =
           let uu____3818 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____3818 in
         match uu____3811 with
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
                      let uu____3874 =
                        let uu____3877 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____3887 = discover (key :: cycle) dep1 in
                               dep1 :: uu____3887) direct_deps in
                        FStar_List.flatten uu____3877 in
                      FStar_List.unique uu____3874 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____3900 =
                       let uu____3903 = FStar_ST.op_Bang topologically_sorted in
                       key :: uu____3903 in
                     FStar_ST.op_Colon_Equals topologically_sorted uu____3900);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____4045 =
           let uu____4054 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____4054 in
         match uu____4045 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____4090 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____4094 = lowercase_module_name f in
                       uu____4094 = k) filenames in
                Prims.op_Negation uu____4090)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____4104 = lowercase_module_name f in
                     uu____4104 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____4106) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____4128 = must_find f in FStar_List.rev uu____4128 in
       let by_target =
         let uu____4140 =
           let uu____4143 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____4143 in
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
                     let uu____4188 =
                       let uu____4197 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____4197 in
                     match uu____4188 with
                     | (FStar_Pervasives_Native.Some intf,uu____4227) when
                         should_append_fsti -> [intf]
                     | uu____4234 -> [] in
                   let deps =
                     let uu____4246 = discover1 k1 in
                     FStar_List.rev uu____4246 in
                   let deps_as_filenames =
                     let uu____4252 = FStar_List.collect must_find deps in
                     FStar_List.append uu____4252 suffix in
                   (f, deps_as_filenames)) as_list) uu____4140 in
       let topologically_sorted1 =
         let uu____4260 = FStar_ST.op_Bang topologically_sorted in
         FStar_List.collect must_find_r uu____4260 in
       FStar_List.iter
         (fun uu____4432  ->
            match uu____4432 with
            | (m1,r) ->
                let uu____4721 =
                  (let uu____4724 = FStar_ST.op_Bang r in
                   Prims.op_Negation uu____4724) &&
                    (let uu____4868 = FStar_Options.interactive () in
                     Prims.op_Negation uu____4868) in
                if uu____4721
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____4871 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____4879 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____4879 = ".fst") in
                    if uu____4871
                    then
                      let uu____4886 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____4886
                    else "" in
                  let uu____4894 =
                    let uu____4895 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____4895 in
                  FStar_Exn.raise uu____4894
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____4944  ->
         match uu____4944 with
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
  fun uu____4992  ->
    match uu____4992 with
    | (make_deps,uu____5016,graph) ->
        let uu____5050 = FStar_Options.dep () in
        (match uu____5050 with
         | FStar_Pervasives_Native.Some "make" -> print_make make_deps
         | FStar_Pervasives_Native.Some "graph" -> print_graph graph
         | FStar_Pervasives_Native.Some uu____5053 ->
             FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
         | FStar_Pervasives_Native.None  -> ())