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
type map = (Prims.string option* Prims.string option) FStar_Util.smap
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
let check_and_strip_suffix: Prims.string -> Prims.string option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____48 =
             (l > lext) &&
               (let uu____59 = FStar_String.substring f (l - lext) lext in
                uu____59 = ext) in
           if uu____48
           then
             let uu____75 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             Some uu____75
           else None) suffixes in
    let uu____87 = FStar_List.filter FStar_Util.is_some matches in
    match uu____87 with | (Some m)::uu____93 -> Some m | uu____97 -> None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____103 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____103 = 'i'
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____113 = is_interface f in Prims.op_Negation uu____113
let list_of_option uu___84_122 =
  match uu___84_122 with | Some x -> [x] | None  -> []
let list_of_pair uu____136 =
  match uu____136 with
  | (intf,impl) ->
      FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____150 =
      let uu____152 = FStar_Util.basename f in
      check_and_strip_suffix uu____152 in
    match uu____150 with
    | Some longname -> FStar_String.lowercase longname
    | None  ->
        let uu____154 =
          let uu____155 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____155 in
        raise uu____154
let build_map:
  Prims.string Prims.list ->
    (Prims.string option* Prims.string option) FStar_Util.smap
  =
  fun filenames  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____168 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____168 in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____186 = FStar_Util.smap_try_find map1 key in
      match uu____186 with
      | Some (intf,impl) ->
          let uu____206 = is_interface full_path in
          if uu____206
          then FStar_Util.smap_add map1 key ((Some full_path), impl)
          else FStar_Util.smap_add map1 key (intf, (Some full_path))
      | None  ->
          let uu____224 = is_interface full_path in
          if uu____224
          then FStar_Util.smap_add map1 key ((Some full_path), None)
          else FStar_Util.smap_add map1 key (None, (Some full_path)) in
    FStar_List.iter
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.iter
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____244 = check_and_strip_suffix f1 in
                match uu____244 with
                | Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1 in
                    let key = FStar_String.lowercase longname in
                    add_entry key full_path
                | None  -> ()) files
         else
           (let uu____251 =
              let uu____252 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____252 in
            raise uu____251)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____255 = lowercase_module_name f in add_entry uu____255 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____270 =
           let uu____272 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____272 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____299 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____299 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.write found true)
              else ()) uu____270);
        FStar_ST.read found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____335 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____335 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____344 = string_of_lid l last1 in
      FStar_String.lowercase uu____344
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____352 =
        let uu____353 =
          let uu____354 =
            let uu____355 =
              let uu____357 = FStar_Util.basename filename in
              check_and_strip_suffix uu____357 in
            FStar_Util.must uu____355 in
          FStar_String.lowercase uu____354 in
        uu____353 <> k' in
      if uu____352
      then
        let uu____358 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____358 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____363 -> false
let collect_one:
  (Prims.string* Prims.bool FStar_ST.ref) Prims.list ->
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
              let uu____398 =
                let uu____399 =
                  let uu____400 = FStar_ST.read deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____400 in
                Prims.op_Negation uu____399 in
              if uu____398
              then
                let uu____406 =
                  let uu____408 = FStar_ST.read deps in d :: uu____408 in
                FStar_ST.write deps uu____406
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____435 = FStar_Util.smap_try_find working_map key in
              match uu____435 with
              | Some pair ->
                  FStar_List.iter
                    (fun f  ->
                       let uu____455 = lowercase_module_name f in
                       add_dep uu____455) (list_of_pair pair)
              | None  ->
                  let r = enter_namespace original_map working_map key in
                  if Prims.op_Negation r
                  then
                    (if let_open
                     then
                       raise
                         (FStar_Errors.Err
                            "let-open only supported for modules, not namespaces")
                     else
                       (let uu____462 = string_of_lid lid true in
                        FStar_Util.print1_warning
                          "Warning: no modules in namespace %s and no file with that name either\n"
                          uu____462))
                  else () in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____473 = FStar_Util.smap_try_find original_map alias in
              match uu____473 with
              | Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | None  ->
                  let uu____500 =
                    let uu____501 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____501 in
                  raise uu____500 in
            let record_lid lid =
              let try_key key =
                let uu____510 = FStar_Util.smap_try_find working_map key in
                match uu____510 with
                | Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____530 = lowercase_module_name f in
                         add_dep uu____530) (list_of_pair pair)
                | None  ->
                    let uu____535 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____535
                    then
                      let uu____542 =
                        FStar_Range.string_of_range
                          (FStar_Ident.range_of_lid lid) in
                      let uu____543 = string_of_lid lid false in
                      FStar_Util.print2_warning
                        "%s (Warning): unbound module reference %s\n"
                        uu____542 uu____543
                    else () in
              let uu____546 = lowercase_join_longident lid false in
              try_key uu____546 in
            let auto_open =
              let uu____549 =
                let uu____550 = FStar_Util.basename filename in
                let uu____551 = FStar_Options.prims_basename () in
                uu____550 = uu____551 in
              if uu____549
              then []
              else
                (let uu____554 =
                   let uu____555 = FStar_Util.basename filename in
                   let uu____556 = FStar_Options.pervasives_basename () in
                   uu____555 = uu____556 in
                 if uu____554
                 then [FStar_Parser_Const.prims_lid]
                 else
                   [FStar_Parser_Const.fstar_ns_lid;
                   FStar_Parser_Const.pervasives_lid;
                   FStar_Parser_Const.prims_lid]) in
            FStar_List.iter (record_open false) auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_fragment uu___85_631 =
               match uu___85_631 with
               | FStar_Util.Inl file -> collect_file file
               | FStar_Util.Inr decls -> collect_decls decls
             and collect_file uu___86_644 =
               match uu___86_644 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.print1_warning
                      "Warning: file %s does not respect the one module per file convention\n"
                      filename;
                    FStar_List.iter collect_module modules)
             and collect_module uu___87_650 =
               match uu___87_650 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____657 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____657
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____658 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____658
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____663  ->
                              match uu____663 with
                              | (m,r) ->
                                  let uu____671 =
                                    let uu____672 =
                                      let uu____673 = string_of_lid lid true in
                                      FStar_String.lowercase uu____673 in
                                    (FStar_String.lowercase m) = uu____672 in
                                  if uu____671
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____679) ->
                   (check_module_declaration_against_filename lid filename;
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____684 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____684
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____685 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____685
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____690  ->
                              match uu____690 with
                              | (m,r) ->
                                  let uu____698 =
                                    let uu____699 =
                                      let uu____700 = string_of_lid lid true in
                                      FStar_String.lowercase uu____700 in
                                    (FStar_String.lowercase m) = uu____699 in
                                  if uu____698
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___88_708 =
               match uu___88_708 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____714 = lowercase_join_longident lid true in
                     add_dep uu____714);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____715,patterms) ->
                   FStar_List.iter
                     (fun uu____725  ->
                        match uu____725 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____732,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____734;
                     FStar_Parser_AST.mdest = uu____735;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____737;
                     FStar_Parser_AST.mdest = uu____738;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____740,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____742;
                     FStar_Parser_AST.mdest = uu____743;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____747,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____762  ->
                          match uu____762 with | (x,doc1) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____770,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____775 -> ()
               | FStar_Parser_AST.Pragma uu____776 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____782 =
                       let uu____783 = FStar_ST.read num_of_toplevelmods in
                       uu____783 > (Prims.parse_int "1") in
                     if uu____782
                     then
                       let uu____786 =
                         let uu____787 =
                           let uu____788 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____788 in
                         FStar_Errors.Err uu____787 in
                       raise uu____786
                     else ()))
             and collect_tycon uu___89_790 =
               match uu___89_790 with
               | FStar_Parser_AST.TyconAbstract (uu____791,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____799,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____809,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____833  ->
                         match uu____833 with
                         | (uu____838,t,uu____840) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____843,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____873  ->
                         match uu____873 with
                         | (uu____880,t,uu____882,uu____883) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___90_888 =
               match uu___90_888 with
               | FStar_Parser_AST.DefineEffect (uu____889,binders,t,decls) ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____899,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___91_907 =
               match uu___91_907 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____908,t);
                   FStar_Parser_AST.brange = uu____910;
                   FStar_Parser_AST.blevel = uu____911;
                   FStar_Parser_AST.aqual = uu____912;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____913,t);
                   FStar_Parser_AST.brange = uu____915;
                   FStar_Parser_AST.blevel = uu____916;
                   FStar_Parser_AST.aqual = uu____917;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____919;
                   FStar_Parser_AST.blevel = uu____920;
                   FStar_Parser_AST.aqual = uu____921;_} -> collect_term t
               | uu____922 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___92_924 =
               match uu___92_924 with
               | FStar_Const.Const_int (uu____925,Some (signedness,width)) ->
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
                   let uu____935 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____935
               | uu____936 -> ()
             and collect_term' uu___93_937 =
               match uu___93_937 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____944 =
                         let uu____945 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____945 in
                       collect_term' uu____944)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____947 -> ()
               | FStar_Parser_AST.Uvar uu____948 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____951) -> record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____972  ->
                         match uu____972 with
                         | (t,uu____976) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____984) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____986,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____998  ->
                         match uu____998 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____1007,t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Seq (t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.If (t1,t2,t3) ->
                   (collect_term t1; collect_term t2; collect_term t3)
               | FStar_Parser_AST.Match (t,bs) ->
                   (collect_term t; collect_branches bs)
               | FStar_Parser_AST.TryWith (t,bs) ->
                   (collect_term t; collect_branches bs)
               | FStar_Parser_AST.Ascribed (t1,t2,None ) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Ascribed (t1,t2,Some tac) ->
                   (collect_term t1; collect_term t2; collect_term tac)
               | FStar_Parser_AST.Record (t,idterms) ->
                   (FStar_Util.iter_opt t collect_term;
                    FStar_List.iter
                      (fun uu____1068  ->
                         match uu____1068 with
                         | (uu____1071,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____1074) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____1112,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____1115,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____1118) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____1122) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____1126,uu____1127) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___94_1133 =
               match uu___94_1133 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____1134 -> ()
               | FStar_Parser_AST.PatConst uu____1135 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____1141 -> ()
               | FStar_Parser_AST.PatName uu____1145 -> ()
               | FStar_Parser_AST.PatTvar uu____1146 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____1155) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____1164  ->
                        match uu____1164 with
                        | (uu____1167,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____1182 =
               match uu____1182 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____1194 = FStar_Parser_Driver.parse_file filename in
             match uu____1194 with
             | (ast,uu____1202) -> (collect_file ast; FStar_ST.read deps))
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let uu____1231 =
     let uu____1232 =
       let uu____1233 =
         let uu____1234 =
           let uu____1236 =
             let uu____1238 = FStar_Util.smap_keys graph in
             FStar_List.unique uu____1238 in
           FStar_List.collect
             (fun k  ->
                let deps =
                  let uu____1246 =
                    let uu____1250 = FStar_Util.smap_try_find graph k in
                    FStar_Util.must uu____1250 in
                  fst uu____1246 in
                let r s = FStar_Util.replace_char s '.' '_' in
                FStar_List.map
                  (fun dep1  ->
                     FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
             uu____1236 in
         FStar_String.concat "\n" uu____1234 in
       Prims.strcat uu____1233 "\n}\n" in
     Prims.strcat "digraph {\n" uu____1232 in
   FStar_Util.write_file "dep.graph" uu____1231)
let collect:
  verify_mode ->
    Prims.string Prims.list ->
      ((Prims.string* Prims.string Prims.list) Prims.list* Prims.string
        Prims.list* (Prims.string Prims.list* color) FStar_Util.smap)
  =
  fun verify_mode  ->
    fun filenames  ->
      let graph = FStar_Util.smap_create (Prims.parse_int "41") in
      let verify_flags =
        let uu____1312 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____1318 = FStar_Util.mk_ref false in (f, uu____1318))
          uu____1312 in
      let partial_discovery =
        let uu____1325 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____1325 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____1331 =
          let uu____1336 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____1336 in
        match uu____1331 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (None ,None ) -> failwith "Impossible"
             | (None ,Some i) -> i
             | (Some i,None ) -> i
             | (Some i,uu____1367) when partial_discovery -> i
             | (Some i,Some j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____1393 =
          let uu____1394 = FStar_Util.smap_try_find graph key in
          uu____1394 = None in
        if uu____1393
        then
          let uu____1409 =
            let uu____1414 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____1414 in
          match uu____1409 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (Some impl1,Some uu____1444) when interface_only -> []
                | (Some impl1,uu____1448) ->
                    collect_one1 is_user_provided_filename m impl1
                | (None ,uu____1452) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____1470 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____1472 = lowercase_module_name f1 in
                     uu____1472 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____1470) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____1497 =
           let uu____1501 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____1501 in
         match uu____1497 with
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
                      let uu____1534 =
                        let uu____1536 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____1541 = discover (key :: cycle) dep1 in
                               dep1 :: uu____1541) direct_deps in
                        FStar_List.flatten uu____1536 in
                      FStar_List.unique uu____1534 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____1549 =
                       let uu____1551 = FStar_ST.read topologically_sorted in
                       key :: uu____1551 in
                     FStar_ST.write topologically_sorted uu____1549);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____1568 =
           let uu____1573 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____1573 in
         match uu____1568 with
         | (Some intf,Some impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____1592 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____1594 = lowercase_module_name f in
                       uu____1594 = k) filenames in
                Prims.op_Negation uu____1592)
             -> [intf; impl]
         | (Some intf,Some impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____1600 = lowercase_module_name f in
                     uu____1600 = k)) filenames
             -> [intf; impl]
         | (Some intf,uu____1602) -> [intf]
         | (None ,Some impl) -> [impl]
         | (None ,None ) -> [] in
       let must_find_r f =
         let uu____1616 = must_find f in FStar_List.rev uu____1616 in
       let by_target =
         let uu____1623 =
           let uu____1625 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____1625 in
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
                     let uu____1651 =
                       let uu____1656 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____1656 in
                     match uu____1651 with
                     | (Some intf,uu____1672) when should_append_fsti ->
                         [intf]
                     | uu____1676 -> [] in
                   let deps =
                     let uu____1683 = discover1 k1 in
                     FStar_List.rev uu____1683 in
                   let deps_as_filenames =
                     let uu____1687 = FStar_List.collect must_find deps in
                     FStar_List.append uu____1687 suffix in
                   (f, deps_as_filenames)) as_list) uu____1623 in
       let topologically_sorted1 =
         let uu____1692 = FStar_ST.read topologically_sorted in
         FStar_List.collect must_find_r uu____1692 in
       FStar_List.iter
         (fun uu____1701  ->
            match uu____1701 with
            | (m1,r) ->
                let uu____1709 =
                  (let uu____1710 = FStar_ST.read r in
                   Prims.op_Negation uu____1710) &&
                    (let uu____1713 = FStar_Options.interactive () in
                     Prims.op_Negation uu____1713) in
                if uu____1709
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____1718 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____1725 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____1725 = ".fst") in
                    if uu____1718
                    then
                      let uu____1732 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____1732
                    else "" in
                  let uu____1740 =
                    let uu____1741 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____1741 in
                  raise uu____1740
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string* Prims.string Prims.list) Prims.list -> Prims.unit =
  fun deps  ->
    FStar_List.iter
      (fun uu____1766  ->
         match uu____1766 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print uu____1796 =
  match uu____1796 with
  | (make_deps,uu____1809,graph) ->
      let uu____1827 = FStar_Options.dep () in
      (match uu____1827 with
       | Some "make" -> print_make make_deps
       | Some "graph" -> print_graph graph
       | Some uu____1829 ->
           raise (FStar_Errors.Err "unknown tool for --dep\n")
       | None  -> ())