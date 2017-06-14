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
  fun projectee  -> match projectee with | White  -> true | uu____21 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____25 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____29 -> false
type open_kind =
  | Open_module
  | Open_namespace
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____33 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____37 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____54 =
             (l > lext) &&
               (let uu____60 = FStar_String.substring f (l - lext) lext in
                uu____60 = ext) in
           if uu____54
           then
             let uu____69 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____69
           else FStar_Pervasives_Native.None) suffixes in
    let uu____76 = FStar_List.filter FStar_Util.is_some matches in
    match uu____76 with
    | (FStar_Pervasives_Native.Some m)::uu____82 ->
        FStar_Pervasives_Native.Some m
    | uu____86 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____92 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____92 = 'i'
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____99 = is_interface f in Prims.op_Negation uu____99
let list_of_option uu___84_108 =
  match uu___84_108 with
  | FStar_Pervasives_Native.Some x -> [x]
  | FStar_Pervasives_Native.None  -> []
let list_of_pair uu____122 =
  match uu____122 with
  | (intf,impl) ->
      FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____136 =
      let uu____138 = FStar_Util.basename f in
      check_and_strip_suffix uu____138 in
    match uu____136 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____140 =
          let uu____141 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____141 in
        raise uu____140
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
      let uu____154 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____154 in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____172 = FStar_Util.smap_try_find map1 key in
      match uu____172 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____192 = is_interface full_path in
          if uu____192
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____210 = is_interface full_path in
          if uu____210
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
                let uu____230 = check_and_strip_suffix f1 in
                match uu____230 with
                | FStar_Pervasives_Native.Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1 in
                    let key = FStar_String.lowercase longname in
                    add_entry key full_path
                | FStar_Pervasives_Native.None  -> ()) files
         else
           (let uu____237 =
              let uu____238 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____238 in
            raise uu____237)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____241 = lowercase_module_name f in add_entry uu____241 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____256 =
           let uu____258 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____258 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____278 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____278 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.write found true)
              else ()) uu____256);
        FStar_ST.read found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____314 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____314 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____323 = string_of_lid l last1 in
      FStar_String.lowercase uu____323
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____327 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____327
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____336 =
        let uu____337 =
          let uu____338 =
            let uu____339 =
              let uu____341 = FStar_Util.basename filename in
              check_and_strip_suffix uu____341 in
            FStar_Util.must uu____339 in
          FStar_String.lowercase uu____338 in
        uu____337 <> k' in
      if uu____336
      then
        let uu____342 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____342 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____347 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____357 = FStar_Options.prims_basename () in
      let uu____358 =
        let uu____360 = FStar_Options.pervasives_basename () in
        let uu____361 =
          let uu____363 = FStar_Options.pervasives_native_basename () in
          [uu____363] in
        uu____360 :: uu____361 in
      uu____357 :: uu____358 in
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
              let uu____412 =
                let uu____413 =
                  let uu____414 = FStar_ST.read deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____414 in
                Prims.op_Negation uu____413 in
              if uu____412
              then
                let uu____420 =
                  let uu____422 = FStar_ST.read deps in d :: uu____422 in
                FStar_ST.write deps uu____420
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module lid =
              let key = lowercase_join_longident lid true in
              let uu____446 = FStar_Util.smap_try_find working_map key in
              match uu____446 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____467 = lowercase_module_name f in
                        add_dep uu____467) (list_of_pair pair);
                   true)
              | FStar_Pervasives_Native.None  -> false in
            let record_open_namespace error_msg lid =
              let key = lowercase_join_longident lid true in
              let r = enter_namespace original_map working_map key in
              if Prims.op_Negation r
              then
                match error_msg with
                | FStar_Pervasives_Native.Some e ->
                    raise (FStar_Errors.Err e)
                | FStar_Pervasives_Native.None  ->
                    let uu____484 = string_of_lid lid true in
                    FStar_Util.print1_warning
                      "Warning: no modules in namespace %s and no file with that name either\n"
                      uu____484
              else () in
            let record_open let_open lid =
              let uu____493 = record_open_module lid in
              if uu____493
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____504 =
              match uu____504 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____509 = record_open_module lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____519 = FStar_Util.smap_try_find original_map alias in
              match uu____519 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____546 =
                    let uu____547 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____547 in
                  raise uu____546 in
            let record_lid lid =
              let try_key key =
                let uu____556 = FStar_Util.smap_try_find working_map key in
                match uu____556 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____576 = lowercase_module_name f in
                         add_dep uu____576) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____581 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____581
                    then
                      let uu____585 =
                        FStar_Range.string_of_range
                          (FStar_Ident.range_of_lid lid) in
                      let uu____586 = string_of_lid lid false in
                      FStar_Util.print2_warning
                        "%s (Warning): unbound module reference %s\n"
                        uu____585 uu____586
                    else () in
              let uu____589 = lowercase_join_longident lid false in
              try_key uu____589 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_fragment uu___85_668 =
               match uu___85_668 with
               | FStar_Util.Inl file -> collect_file file
               | FStar_Util.Inr decls -> collect_decls decls
             and collect_file uu___86_681 =
               match uu___86_681 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.print1_warning
                      "Warning: file %s does not respect the one module per file convention\n"
                      filename;
                    FStar_List.iter collect_module modules)
             and collect_module uu___87_687 =
               match uu___87_687 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____697 =
                         let uu____698 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____698 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____701 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____701
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____702 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____702
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____707  ->
                              match uu____707 with
                              | (m,r) ->
                                  let uu____715 =
                                    let uu____716 =
                                      let uu____717 = string_of_lid lid true in
                                      FStar_String.lowercase uu____717 in
                                    (FStar_String.lowercase m) = uu____716 in
                                  if uu____715
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____723) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____731 =
                         let uu____732 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____732 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____735 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____735
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____736 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____736
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____741  ->
                              match uu____741 with
                              | (m,r) ->
                                  let uu____749 =
                                    let uu____750 =
                                      let uu____751 = string_of_lid lid true in
                                      FStar_String.lowercase uu____751 in
                                    (FStar_String.lowercase m) = uu____750 in
                                  if uu____749
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___88_759 =
               match uu___88_759 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____765 = lowercase_join_longident lid true in
                     add_dep uu____765);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____766,patterms) ->
                   FStar_List.iter
                     (fun uu____776  ->
                        match uu____776 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____783,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____785;
                     FStar_Parser_AST.mdest = uu____786;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____788;
                     FStar_Parser_AST.mdest = uu____789;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____791,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____793;
                     FStar_Parser_AST.mdest = uu____794;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____798,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____813  ->
                          match uu____813 with | (x,doc1) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____821,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____826 -> ()
               | FStar_Parser_AST.Pragma uu____827 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____833 =
                       let uu____834 = FStar_ST.read num_of_toplevelmods in
                       uu____834 > (Prims.parse_int "1") in
                     if uu____833
                     then
                       let uu____837 =
                         let uu____838 =
                           let uu____839 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____839 in
                         FStar_Errors.Err uu____838 in
                       raise uu____837
                     else ()))
             and collect_tycon uu___89_841 =
               match uu___89_841 with
               | FStar_Parser_AST.TyconAbstract (uu____842,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____850,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____860,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____884  ->
                         match uu____884 with
                         | (uu____889,t,uu____891) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____894,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____924  ->
                         match uu____924 with
                         | (uu____931,t,uu____933,uu____934) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___90_939 =
               match uu___90_939 with
               | FStar_Parser_AST.DefineEffect (uu____940,binders,t,decls) ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____950,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___91_958 =
               match uu___91_958 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____959,t);
                   FStar_Parser_AST.brange = uu____961;
                   FStar_Parser_AST.blevel = uu____962;
                   FStar_Parser_AST.aqual = uu____963;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____964,t);
                   FStar_Parser_AST.brange = uu____966;
                   FStar_Parser_AST.blevel = uu____967;
                   FStar_Parser_AST.aqual = uu____968;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____970;
                   FStar_Parser_AST.blevel = uu____971;
                   FStar_Parser_AST.aqual = uu____972;_} -> collect_term t
               | uu____973 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___92_975 =
               match uu___92_975 with
               | FStar_Const.Const_int
                   (uu____976,FStar_Pervasives_Native.Some
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
                   let uu____986 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____986
               | uu____987 -> ()
             and collect_term' uu___93_988 =
               match uu___93_988 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____995 =
                         let uu____996 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____996 in
                       collect_term' uu____995)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____998 -> ()
               | FStar_Parser_AST.Uvar uu____999 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____1002) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____1021  ->
                         match uu____1021 with
                         | (t,uu____1025) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____1033) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____1035,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____1047  ->
                         match uu____1047 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____1056,t1,t2) ->
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
                      (fun uu____1117  ->
                         match uu____1117 with
                         | (uu____1120,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____1123) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____1161,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____1164,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____1167) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____1171) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____1175,uu____1176) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___94_1182 =
               match uu___94_1182 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____1183 -> ()
               | FStar_Parser_AST.PatConst uu____1184 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____1190 -> ()
               | FStar_Parser_AST.PatName uu____1194 -> ()
               | FStar_Parser_AST.PatTvar uu____1195 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____1204) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____1213  ->
                        match uu____1213 with
                        | (uu____1216,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____1231 =
               match uu____1231 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____1243 = FStar_Parser_Driver.parse_file filename in
             match uu____1243 with
             | (ast,uu____1251) -> (collect_file ast; FStar_ST.read deps))
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let uu____1280 =
     let uu____1281 =
       let uu____1282 =
         let uu____1283 =
           let uu____1285 =
             let uu____1287 = FStar_Util.smap_keys graph in
             FStar_List.unique uu____1287 in
           FStar_List.collect
             (fun k  ->
                let deps =
                  let uu____1295 =
                    let uu____1299 = FStar_Util.smap_try_find graph k in
                    FStar_Util.must uu____1299 in
                  FStar_Pervasives_Native.fst uu____1295 in
                let r s = FStar_Util.replace_char s '.' '_' in
                FStar_List.map
                  (fun dep1  ->
                     FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
             uu____1285 in
         FStar_String.concat "\n" uu____1283 in
       Prims.strcat uu____1282 "\n}\n" in
     Prims.strcat "digraph {\n" uu____1281 in
   FStar_Util.write_file "dep.graph" uu____1280)
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
        let uu____1361 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____1367 = FStar_Util.mk_ref false in (f, uu____1367))
          uu____1361 in
      let partial_discovery =
        let uu____1374 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____1374 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____1380 =
          let uu____1385 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____1385 in
        match uu____1380 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____1416) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____1442 =
          let uu____1443 = FStar_Util.smap_try_find graph key in
          uu____1443 = FStar_Pervasives_Native.None in
        if uu____1442
        then
          let uu____1458 =
            let uu____1463 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____1463 in
          match uu____1458 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____1493) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____1497) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____1501) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____1519 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____1521 = lowercase_module_name f1 in
                     uu____1521 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____1519) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____1546 =
           let uu____1550 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____1550 in
         match uu____1546 with
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
                      let uu____1583 =
                        let uu____1585 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____1590 = discover (key :: cycle) dep1 in
                               dep1 :: uu____1590) direct_deps in
                        FStar_List.flatten uu____1585 in
                      FStar_List.unique uu____1583 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____1598 =
                       let uu____1600 = FStar_ST.read topologically_sorted in
                       key :: uu____1600 in
                     FStar_ST.write topologically_sorted uu____1598);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____1617 =
           let uu____1622 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____1622 in
         match uu____1617 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____1641 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____1643 = lowercase_module_name f in
                       uu____1643 = k) filenames in
                Prims.op_Negation uu____1641)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____1649 = lowercase_module_name f in
                     uu____1649 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____1651) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____1665 = must_find f in FStar_List.rev uu____1665 in
       let by_target =
         let uu____1672 =
           let uu____1674 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____1674 in
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
                     let uu____1698 =
                       let uu____1703 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____1703 in
                     match uu____1698 with
                     | (FStar_Pervasives_Native.Some intf,uu____1719) when
                         should_append_fsti -> [intf]
                     | uu____1723 -> [] in
                   let deps =
                     let uu____1730 = discover1 k1 in
                     FStar_List.rev uu____1730 in
                   let deps_as_filenames =
                     let uu____1734 = FStar_List.collect must_find deps in
                     FStar_List.append uu____1734 suffix in
                   (f, deps_as_filenames)) as_list) uu____1672 in
       let topologically_sorted1 =
         let uu____1739 = FStar_ST.read topologically_sorted in
         FStar_List.collect must_find_r uu____1739 in
       FStar_List.iter
         (fun uu____1748  ->
            match uu____1748 with
            | (m1,r) ->
                let uu____1756 =
                  (let uu____1757 = FStar_ST.read r in
                   Prims.op_Negation uu____1757) &&
                    (let uu____1760 = FStar_Options.interactive () in
                     Prims.op_Negation uu____1760) in
                if uu____1756
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____1764 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____1768 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____1768 = ".fst") in
                    if uu____1764
                    then
                      let uu____1772 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____1772
                    else "" in
                  let uu____1777 =
                    let uu____1778 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____1778 in
                  raise uu____1777
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____1803  ->
         match uu____1803 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print uu____1833 =
  match uu____1833 with
  | (make_deps,uu____1846,graph) ->
      let uu____1864 = FStar_Options.dep () in
      (match uu____1864 with
       | FStar_Pervasives_Native.Some "make" -> print_make make_deps
       | FStar_Pervasives_Native.Some "graph" -> print_graph graph
       | FStar_Pervasives_Native.Some uu____1866 ->
           raise (FStar_Errors.Err "unknown tool for --dep\n")
       | FStar_Pervasives_Native.None  -> ())