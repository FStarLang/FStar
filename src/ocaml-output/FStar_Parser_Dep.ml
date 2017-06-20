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
           let uu____51 =
             (l > lext) &&
               (let uu____58 = FStar_String.substring f (l - lext) lext in
                uu____58 = ext) in
           if uu____51
           then
             let uu____67 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             Some uu____67
           else None) suffixes in
    let uu____74 = FStar_List.filter FStar_Util.is_some matches in
    match uu____74 with | (Some m)::uu____80 -> Some m | uu____84 -> None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____90 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____90 = 'i'
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____97 = is_interface f in Prims.op_Negation uu____97
let list_of_option uu___83_106 =
  match uu___83_106 with | Some x -> [x] | None  -> []
let list_of_pair uu____120 =
  match uu____120 with
  | (intf,impl) ->
      FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____134 =
      let uu____136 = FStar_Util.basename f in
      check_and_strip_suffix uu____136 in
    match uu____134 with
    | Some longname -> FStar_String.lowercase longname
    | None  ->
        let uu____138 =
          let uu____139 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____139 in
        raise uu____138
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
      let uu____152 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____152 in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____170 = FStar_Util.smap_try_find map1 key in
      match uu____170 with
      | Some (intf,impl) ->
          let uu____190 = is_interface full_path in
          if uu____190
          then FStar_Util.smap_add map1 key ((Some full_path), impl)
          else FStar_Util.smap_add map1 key (intf, (Some full_path))
      | None  ->
          let uu____208 = is_interface full_path in
          if uu____208
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
                let uu____236 = check_and_strip_suffix f1 in
                match uu____236 with
                | Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1 in
                    let key = FStar_String.lowercase longname in
                    add_entry key full_path
                | None  -> ()) files
         else
           (let uu____243 =
              let uu____244 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____244 in
            raise uu____243)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____249 = lowercase_module_name f in add_entry uu____249 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____264 =
           let uu____266 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____266 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____290 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____290 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.write found true)
              else ()) uu____264);
        FStar_ST.read found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____326 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____326 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____336 = string_of_lid l last1 in
      FStar_String.lowercase uu____336
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____344 =
        let uu____345 =
          let uu____346 =
            let uu____347 =
              let uu____349 = FStar_Util.basename filename in
              check_and_strip_suffix uu____349 in
            FStar_Util.must uu____347 in
          FStar_String.lowercase uu____346 in
        uu____345 <> k' in
      if uu____344
      then
        let uu____350 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____350 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____355 -> false
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
              let uu____390 =
                let uu____391 =
                  let uu____392 = FStar_ST.read deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____392 in
                Prims.op_Negation uu____391 in
              if uu____390
              then
                let uu____399 =
                  let uu____401 = FStar_ST.read deps in d :: uu____401 in
                FStar_ST.write deps uu____399
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____428 = FStar_Util.smap_try_find working_map key in
              match uu____428 with
              | Some pair ->
                  FStar_List.iter
                    (fun f  ->
                       let uu____450 = lowercase_module_name f in
                       add_dep uu____450) (list_of_pair pair)
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
                       (let uu____457 = string_of_lid lid true in
                        FStar_Util.print1_warning
                          "Warning: no modules in namespace %s and no file with that name either\n"
                          uu____457))
                  else () in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____468 = FStar_Util.smap_try_find original_map alias in
              match uu____468 with
              | Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | None  ->
                  let uu____495 =
                    let uu____496 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____496 in
                  raise uu____495 in
            let record_lid lid =
              let try_key key =
                let uu____505 = FStar_Util.smap_try_find working_map key in
                match uu____505 with
                | Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____527 = lowercase_module_name f in
                         add_dep uu____527) (list_of_pair pair)
                | None  ->
                    let uu____532 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____532
                    then
                      let uu____536 =
                        FStar_Range.string_of_range
                          (FStar_Ident.range_of_lid lid) in
                      let uu____537 = string_of_lid lid false in
                      FStar_Util.print2_warning
                        "%s (Warning): unbound module reference %s\n"
                        uu____536 uu____537
                    else () in
              let uu____540 = lowercase_join_longident lid false in
              try_key uu____540 in
            let auto_open =
              let uu____543 =
                let uu____544 = FStar_Util.basename filename in
                let uu____545 = FStar_Options.prims_basename () in
                uu____544 = uu____545 in
              if uu____543
              then []
              else
                (let uu____548 =
                   let uu____549 = FStar_Util.basename filename in
                   let uu____550 = FStar_Options.pervasives_basename () in
                   uu____549 = uu____550 in
                 if uu____548
                 then [FStar_Parser_Const.prims_lid]
                 else
                   [FStar_Parser_Const.fstar_ns_lid;
                   FStar_Parser_Const.pervasives_lid;
                   FStar_Parser_Const.prims_lid]) in
            FStar_List.iter (record_open false) auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_file uu___84_618 =
               match uu___84_618 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.print1_warning
                      "Warning: file %s does not respect the one module per file convention\n"
                      filename;
                    FStar_List.iter collect_module modules)
             and collect_module uu___85_624 =
               match uu___85_624 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____631 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____631
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____632 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____632
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____641  ->
                              match uu____641 with
                              | (m,r) ->
                                  let uu____649 =
                                    let uu____650 =
                                      let uu____651 = string_of_lid lid true in
                                      FStar_String.lowercase uu____651 in
                                    (FStar_String.lowercase m) = uu____650 in
                                  if uu____649
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____657) ->
                   (check_module_declaration_against_filename lid filename;
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____662 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____662
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____663 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____663
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____672  ->
                              match uu____672 with
                              | (m,r) ->
                                  let uu____680 =
                                    let uu____681 =
                                      let uu____682 = string_of_lid lid true in
                                      FStar_String.lowercase uu____682 in
                                    (FStar_String.lowercase m) = uu____681 in
                                  if uu____680
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___86_692 =
               match uu___86_692 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____698 = lowercase_join_longident lid true in
                     add_dep uu____698);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____699,patterms) ->
                   FStar_List.iter
                     (fun uu____713  ->
                        match uu____713 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____720,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____722;
                     FStar_Parser_AST.mdest = uu____723;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____725;
                     FStar_Parser_AST.mdest = uu____726;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____728,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____730;
                     FStar_Parser_AST.mdest = uu____731;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____735,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____753  ->
                          match uu____753 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____761,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____766 -> ()
               | FStar_Parser_AST.Pragma uu____767 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____773 =
                       let uu____774 = FStar_ST.read num_of_toplevelmods in
                       uu____774 > (Prims.parse_int "1") in
                     if uu____773
                     then
                       let uu____777 =
                         let uu____778 =
                           let uu____779 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____779 in
                         FStar_Errors.Err uu____778 in
                       raise uu____777
                     else ()))
             and collect_tycon uu___87_781 =
               match uu___87_781 with
               | FStar_Parser_AST.TyconAbstract (uu____782,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____790,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____800,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____828  ->
                         match uu____828 with
                         | (uu____833,t,uu____835) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____838,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____873  ->
                         match uu____873 with
                         | (uu____880,t,uu____882,uu____883) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___88_888 =
               match uu___88_888 with
               | FStar_Parser_AST.DefineEffect (uu____889,binders,t,decls) ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____899,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___89_907 =
               match uu___89_907 with
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
             and collect_constant uu___90_924 =
               match uu___90_924 with
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
             and collect_term' uu___91_937 =
               match uu___91_937 with
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
                      (fun uu____973  ->
                         match uu____973 with
                         | (t,uu____977) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____985) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____987,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____1003  ->
                         match uu____1003 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____1012,t1,t2) ->
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
                      (fun uu____1076  ->
                         match uu____1076 with
                         | (uu____1079,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____1082) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____1120,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____1123,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____1126) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____1130) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____1134,uu____1135) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___92_1141 =
               match uu___92_1141 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____1142 -> ()
               | FStar_Parser_AST.PatConst uu____1143 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____1149 -> ()
               | FStar_Parser_AST.PatName uu____1153 -> ()
               | FStar_Parser_AST.PatTvar uu____1154 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____1163) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____1175  ->
                        match uu____1175 with
                        | (uu____1178,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____1193 =
               match uu____1193 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____1205 = FStar_Parser_Driver.parse_file filename in
             match uu____1205 with
             | (ast,uu____1213) -> (collect_file ast; FStar_ST.read deps))
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let uu____1242 =
     let uu____1243 =
       let uu____1244 =
         let uu____1245 =
           let uu____1247 =
             let uu____1249 = FStar_Util.smap_keys graph in
             FStar_List.unique uu____1249 in
           FStar_List.collect
             (fun k  ->
                let deps =
                  let uu____1260 =
                    let uu____1264 = FStar_Util.smap_try_find graph k in
                    FStar_Util.must uu____1264 in
                  fst uu____1260 in
                let r s = FStar_Util.replace_char s '.' '_' in
                FStar_List.map
                  (fun dep1  ->
                     FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
             uu____1247 in
         FStar_String.concat "\n" uu____1245 in
       Prims.strcat uu____1244 "\n}\n" in
     Prims.strcat "digraph {\n" uu____1243 in
   FStar_Util.write_file "dep.graph" uu____1242)
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
        let uu____1315 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____1323 = FStar_Util.mk_ref false in (f, uu____1323))
          uu____1315 in
      let partial_discovery =
        let uu____1330 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____1330 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____1336 =
          let uu____1341 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____1341 in
        match uu____1336 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (None ,None ) -> failwith "Impossible"
             | (None ,Some i) -> i
             | (Some i,None ) -> i
             | (Some i,uu____1372) when partial_discovery -> i
             | (Some i,Some j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____1398 =
          let uu____1399 = FStar_Util.smap_try_find graph key in
          uu____1399 = None in
        if uu____1398
        then
          let uu____1414 =
            let uu____1419 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____1419 in
          match uu____1414 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (Some impl1,Some uu____1449) when interface_only -> []
                | (Some impl1,uu____1453) ->
                    collect_one1 is_user_provided_filename m impl1
                | (None ,uu____1457) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____1476 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____1481 = lowercase_module_name f1 in
                     uu____1481 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____1476) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____1506 =
           let uu____1510 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____1510 in
         match uu____1506 with
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
                      let uu____1543 =
                        let uu____1545 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____1552 = discover (key :: cycle) dep1 in
                               dep1 :: uu____1552) direct_deps in
                        FStar_List.flatten uu____1545 in
                      FStar_List.unique uu____1543 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____1560 =
                       let uu____1562 = FStar_ST.read topologically_sorted in
                       key :: uu____1562 in
                     FStar_ST.write topologically_sorted uu____1560);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____1579 =
           let uu____1584 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____1584 in
         match uu____1579 with
         | (Some intf,Some impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____1604 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____1608 = lowercase_module_name f in
                       uu____1608 = k) filenames in
                Prims.op_Negation uu____1604)
             -> [intf; impl]
         | (Some intf,Some impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____1616 = lowercase_module_name f in
                     uu____1616 = k)) filenames
             -> [intf; impl]
         | (Some intf,uu____1618) -> [intf]
         | (None ,Some impl) -> [impl]
         | (None ,None ) -> [] in
       let must_find_r f =
         let uu____1632 = must_find f in FStar_List.rev uu____1632 in
       let by_target =
         let uu____1639 =
           let uu____1641 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____1641 in
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
                     let uu____1676 =
                       let uu____1681 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____1681 in
                     match uu____1676 with
                     | (Some intf,uu____1697) when should_append_fsti ->
                         [intf]
                     | uu____1701 -> [] in
                   let deps =
                     let uu____1708 = discover1 k1 in
                     FStar_List.rev uu____1708 in
                   let deps_as_filenames =
                     let uu____1712 = FStar_List.collect must_find deps in
                     FStar_List.append uu____1712 suffix in
                   (f, deps_as_filenames)) as_list) uu____1639 in
       let topologically_sorted1 =
         let uu____1717 = FStar_ST.read topologically_sorted in
         FStar_List.collect must_find_r uu____1717 in
       FStar_List.iter
         (fun uu____1732  ->
            match uu____1732 with
            | (m1,r) ->
                let uu____1740 =
                  (let uu____1743 = FStar_ST.read r in
                   Prims.op_Negation uu____1743) &&
                    (let uu____1747 = FStar_Options.interactive () in
                     Prims.op_Negation uu____1747) in
                if uu____1740
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____1751 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____1756 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____1756 = ".fst") in
                    if uu____1751
                    then
                      let uu____1760 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____1760
                    else "" in
                  let uu____1765 =
                    let uu____1766 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____1766 in
                  raise uu____1765
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string* Prims.string Prims.list) Prims.list -> Prims.unit =
  fun deps  ->
    FStar_List.iter
      (fun uu____1795  ->
         match uu____1795 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print uu____1826 =
  match uu____1826 with
  | (make_deps,uu____1839,graph) ->
      let uu____1857 = FStar_Options.dep () in
      (match uu____1857 with
       | Some "make" -> print_make make_deps
       | Some "graph" -> print_graph graph
       | Some uu____1859 ->
           raise (FStar_Errors.Err "unknown tool for --dep\n")
       | None  -> ())