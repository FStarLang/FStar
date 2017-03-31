open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let uu___is_VerifyAll : verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____4 -> false
  
let uu___is_VerifyUserList : verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____8 -> false
  
let uu___is_VerifyFigureItOut : verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____12 -> false
  
type map =
  (Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let uu___is_White : color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____21 -> false 
let uu___is_Gray : color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____25 -> false 
let uu___is_Black : color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____29 -> false 
let check_and_strip_suffix : Prims.string -> Prims.string Prims.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____46 =
             (l > lext) &&
               (let uu____52 = FStar_String.substring f (l - lext) lext  in
                uu____52 = ext)
              in
           if uu____46
           then
             let uu____61 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             Some uu____61
           else None) suffixes
       in
    let uu____68 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____68 with | (Some m)::uu____74 -> Some m | uu____78 -> None
  
let is_interface : Prims.string -> Prims.bool =
  fun f  ->
    let uu____84 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____84 = 'i'
  
let is_implementation : Prims.string -> Prims.bool =
  fun f  -> let uu____91 = is_interface f  in Prims.op_Negation uu____91 
let list_of_option uu___113_100 =
  match uu___113_100 with | Some x -> [x] | None  -> [] 
let list_of_pair uu____114 =
  match uu____114 with
  | (intf,impl) ->
      FStar_List.append (list_of_option intf) (list_of_option impl)
  
let lowercase_module_name : Prims.string -> Prims.string =
  fun f  ->
    let uu____128 =
      let uu____130 = FStar_Util.basename f  in
      check_and_strip_suffix uu____130  in
    match uu____128 with
    | Some longname -> FStar_String.lowercase longname
    | None  ->
        let uu____132 =
          let uu____133 = FStar_Util.format1 "not a valid FStar file: %s\n" f
             in
          FStar_Errors.Err uu____133  in
        Prims.raise uu____132
  
let try_convert_file_name_to_windows : Prims.string -> Prims.string =
  fun s  ->
    try
      let uu____138 = FStar_Util.run_proc "which" "cygpath" ""  in
      match uu____138 with
      | (uu____142,t_out,uu____144) ->
          if
            Prims.op_Negation
              ((FStar_Util.trim_string t_out) = "/usr/bin/cygpath")
          then s
          else
            (let uu____146 =
               FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) ""  in
             match uu____146 with
             | (uu____150,t_out1,uu____152) -> FStar_Util.trim_string t_out1)
    with | uu____154 -> s
  
let build_map :
  Prims.string Prims.list ->
    (Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap
  =
  fun filenames  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map try_convert_file_name_to_windows include_directories  in
    let include_directories2 =
      FStar_List.map FStar_Util.normalize_file_path include_directories1  in
    let include_directories3 = FStar_List.unique include_directories2  in
    let cwd =
      let uu____169 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____169  in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____187 = FStar_Util.smap_try_find map1 key  in
      match uu____187 with
      | Some (intf,impl) ->
          let uu____207 = is_interface full_path  in
          if uu____207
          then FStar_Util.smap_add map1 key ((Some full_path), impl)
          else FStar_Util.smap_add map1 key (intf, (Some full_path))
      | None  ->
          let uu____225 = is_interface full_path  in
          if uu____225
          then FStar_Util.smap_add map1 key ((Some full_path), None)
          else FStar_Util.smap_add map1 key (None, (Some full_path))
       in
    FStar_List.iter
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.iter
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____245 = check_and_strip_suffix f1  in
                match uu____245 with
                | Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1  in
                    let key = FStar_String.lowercase longname  in
                    add_entry key full_path
                | None  -> ()) files
         else
           (let uu____252 =
              let uu____253 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              FStar_Errors.Err uu____253  in
            Prims.raise uu____252)) include_directories3;
    FStar_List.iter
      (fun f  ->
         let uu____256 = lowercase_module_name f  in add_entry uu____256 f)
      filenames;
    map1
  
let enter_namespace : map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false  in
        let prefix2 = Prims.strcat prefix1 "."  in
        (let uu____271 =
           let uu____273 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____273  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____293 = FStar_Util.smap_try_find original_map k  in
                  FStar_Util.must uu____293  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.write found true)
              else ()) uu____271);
        FStar_ST.read found
  
let string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____329 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____329 suffix  in
      FStar_String.concat "." names
  
let lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____338 = string_of_lid l last1  in
      FStar_String.lowercase uu____338
  
let check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____346 =
        let uu____347 =
          let uu____348 =
            let uu____349 =
              let uu____351 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____351  in
            FStar_Util.must uu____349  in
          FStar_String.lowercase uu____348  in
        uu____347 <> k'  in
      if uu____346
      then
        let uu____352 =
          let uu____354 = string_of_lid lid true  in [uu____354; filename]
           in
        FStar_Util.fprint FStar_Util.stderr
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____352
      else ()
  
exception Exit 
let uu___is_Exit : Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____359 -> false 
let collect_one :
  (Prims.string * Prims.bool FStar_ST.ref) Prims.list ->
    verify_mode ->
      Prims.bool -> map -> Prims.string -> Prims.string Prims.list
  =
  fun verify_flags  ->
    fun verify_mode  ->
      fun is_user_provided_filename  ->
        fun original_map  ->
          fun filename  ->
            let deps = FStar_Util.mk_ref []  in
            let add_dep d =
              let uu____394 =
                let uu____395 =
                  let uu____396 = FStar_ST.read deps  in
                  FStar_List.existsb (fun d'  -> d' = d) uu____396  in
                Prims.op_Negation uu____395  in
              if uu____394
              then
                let uu____402 =
                  let uu____404 = FStar_ST.read deps  in d :: uu____404  in
                FStar_ST.write deps uu____402
              else ()  in
            let working_map = FStar_Util.smap_copy original_map  in
            let record_open let_open lid =
              let key = lowercase_join_longident lid true  in
              let uu____431 = FStar_Util.smap_try_find working_map key  in
              match uu____431 with
              | Some pair ->
                  FStar_List.iter
                    (fun f  ->
                       let uu____451 = lowercase_module_name f  in
                       add_dep uu____451) (list_of_pair pair)
              | None  ->
                  let r = enter_namespace original_map working_map key  in
                  if Prims.op_Negation r
                  then
                    (if let_open
                     then
                       Prims.raise
                         (FStar_Errors.Err
                            "let-open only supported for modules, not namespaces")
                     else
                       (let uu____458 =
                          let uu____460 = string_of_lid lid true  in
                          [uu____460]  in
                        FStar_Util.fprint FStar_Util.stderr
                          "Warning: no modules in namespace %s and no file with that name either\n"
                          uu____458))
                  else ()
               in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident)
                 in
              let alias = lowercase_join_longident lid true  in
              let uu____471 = FStar_Util.smap_try_find original_map alias  in
              match uu____471 with
              | Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | None  ->
                  let uu____498 =
                    let uu____499 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias
                       in
                    FStar_Errors.Err uu____499  in
                  Prims.raise uu____498
               in
            let record_lid lid =
              let try_key key =
                let uu____508 = FStar_Util.smap_try_find working_map key  in
                match uu____508 with
                | Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____528 = lowercase_module_name f  in
                         add_dep uu____528) (list_of_pair pair)
                | None  ->
                    let uu____533 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ())
                       in
                    if uu____533
                    then
                      let uu____537 =
                        let uu____539 = string_of_lid lid false  in
                        [uu____539]  in
                      FStar_Util.fprint FStar_Util.stderr
                        "Warning: unbound module reference %s\n" uu____537
                    else ()
                 in
              let uu____542 = lowercase_join_longident lid false  in
              try_key uu____542  in
            let auto_open =
              let uu____545 =
                let uu____546 = FStar_Util.basename filename  in
                uu____546 = "prims.fst"  in
              if uu____545
              then []
              else
                [FStar_Syntax_Const.fstar_ns_lid;
                FStar_Syntax_Const.prims_lid]
               in
            FStar_List.iter (record_open false) auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0")  in
             let rec collect_fragment uu___114_621 =
               match uu___114_621 with
               | FStar_Util.Inl file -> collect_file file
               | FStar_Util.Inr decls -> collect_decls decls
             
             and collect_file uu___115_634 =
               match uu___115_634 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.fprint FStar_Util.stderr
                      "Warning: file %s does not respect the one module per file convention\n"
                      [filename];
                    FStar_List.iter collect_module modules)
             
             and collect_module uu___116_640 =
               match uu___116_640 with
               | FStar_Parser_AST.Module (lid,decls)
                 |FStar_Parser_AST.Interface (lid,decls,_) ->
                   (check_module_declaration_against_filename lid filename;
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____650 = string_of_lid lid true  in
                         FStar_Options.add_verify_module uu____650
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____651 = string_of_lid lid true  in
                           FStar_Options.add_verify_module uu____651
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____656  ->
                              match uu____656 with
                              | (m,r) ->
                                  let uu____664 =
                                    let uu____665 =
                                      let uu____666 = string_of_lid lid true
                                         in
                                      FStar_String.lowercase uu____666  in
                                    (FStar_String.lowercase m) = uu____665
                                     in
                                  if uu____664
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
             
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             
             and collect_decl uu___117_674 =
               match uu___117_674 with
               | FStar_Parser_AST.Include lid|FStar_Parser_AST.Open lid ->
                   record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____679 = lowercase_join_longident lid true  in
                     add_dep uu____679);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____680,patterms) ->
                   FStar_List.iter
                     (fun uu____690  ->
                        match uu____690 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t
                 |FStar_Parser_AST.Assume (_,t)
                  |FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.effect_binders = _;
                     FStar_Parser_AST.msource = _;
                     FStar_Parser_AST.mdest = _;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   |FStar_Parser_AST.SubEffect
                    { FStar_Parser_AST.effect_binders = _;
                      FStar_Parser_AST.msource = _;
                      FStar_Parser_AST.mdest = _;
                      FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                        t;_}|FStar_Parser_AST.Val (_,t)
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.effect_binders = uu____705;
                     FStar_Parser_AST.msource = uu____706;
                     FStar_Parser_AST.mdest = uu____707;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____712,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____727  ->
                          match uu____727 with | (x,doc1) -> x) ts
                      in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____735,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffectForFree ed
                 |FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc _|FStar_Parser_AST.Pragma _ -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____747 =
                       let uu____748 = FStar_ST.read num_of_toplevelmods  in
                       uu____748 > (Prims.parse_int "1")  in
                     if uu____747
                     then
                       let uu____751 =
                         let uu____752 =
                           let uu____753 = string_of_lid lid true  in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____753
                            in
                         FStar_Errors.Err uu____752  in
                       Prims.raise uu____751
                     else ()))
             
             and collect_tycon uu___118_755 =
               match uu___118_755 with
               | FStar_Parser_AST.TyconAbstract (uu____756,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____764,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____774,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____798  ->
                         match uu____798 with
                         | (uu____803,t,uu____805) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____808,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____838  ->
                         match uu____838 with
                         | (uu____845,t,uu____847,uu____848) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             
             and collect_effect_decl uu___119_853 =
               match uu___119_853 with
               | FStar_Parser_AST.DefineEffect
                   (uu____854,binders,t,decls,actions) ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls;
                    collect_decls actions)
               | FStar_Parser_AST.RedefineEffect (uu____868,binders,t) ->
                   (collect_binders binders; collect_term t)
             
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             
             and collect_binder uu___120_876 =
               match uu___120_876 with
               | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_,t);
                   FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _;
                   FStar_Parser_AST.aqual = _;_}
                 |{ FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_,t);
                    FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _;
                    FStar_Parser_AST.aqual = _;_}
                  |{ FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                     FStar_Parser_AST.brange = _;
                     FStar_Parser_AST.blevel = _;
                     FStar_Parser_AST.aqual = _;_}
                   -> collect_term t
               | uu____889 -> ()
             
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             
             and collect_constant uu___121_891 =
               match uu___121_891 with
               | FStar_Const.Const_int (uu____892,Some (signedness,width)) ->
                   let u =
                     match signedness with
                     | FStar_Const.Unsigned  -> "u"
                     | FStar_Const.Signed  -> ""  in
                   let w =
                     match width with
                     | FStar_Const.Int8  -> "8"
                     | FStar_Const.Int16  -> "16"
                     | FStar_Const.Int32  -> "32"
                     | FStar_Const.Int64  -> "64"  in
                   let uu____902 = FStar_Util.format2 "fstar.%sint%s" u w  in
                   add_dep uu____902
               | uu____903 -> ()
             
             and collect_term' uu___122_904 =
               match uu___122_904 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if s = "@"
                    then
                      (let uu____911 =
                         let uu____912 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange
                            in
                         FStar_Parser_AST.Name uu____912  in
                       collect_term' uu____911)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar _|FStar_Parser_AST.Uvar _ -> ()
               | FStar_Parser_AST.Var lid
                 |FStar_Parser_AST.Projector (lid,_)
                  |FStar_Parser_AST.Discrim lid|FStar_Parser_AST.Name lid ->
                   record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____934  ->
                         match uu____934 with
                         | (t,uu____938) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____946) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____948,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____960  ->
                         match uu____960 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Seq (t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.If (t1,t2,t3) ->
                   (collect_term t1; collect_term t2; collect_term t3)
               | FStar_Parser_AST.Match (t,bs)|FStar_Parser_AST.TryWith
                 (t,bs) -> (collect_term t; collect_branches bs)
               | FStar_Parser_AST.Ascribed (t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Record (t,idterms) ->
                   (FStar_Util.iter_opt t collect_term;
                    FStar_List.iter
                      (fun uu____1016  ->
                         match uu____1016 with
                         | (uu____1019,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____1022) -> collect_term t
               | FStar_Parser_AST.Product (binders,t)|FStar_Parser_AST.Sum
                 (binders,t) -> (collect_binders binders; collect_term t)
               | FStar_Parser_AST.QForall (binders,ts,t)
                 |FStar_Parser_AST.QExists (binders,ts,t) ->
                   (collect_binders binders;
                    FStar_List.iter (FStar_List.iter collect_term) ts;
                    collect_term t)
               | FStar_Parser_AST.Refine (binder,t) ->
                   (collect_binder binder; collect_term t)
               | FStar_Parser_AST.NamedTyp (uu____1051,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (_,t)
                 |FStar_Parser_AST.Requires (t,_)
                  |FStar_Parser_AST.Ensures (t,_)|FStar_Parser_AST.Labeled
                   (t,_,_) -> collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             
             and collect_pattern' uu___123_1067 =
               match uu___123_1067 with
               | FStar_Parser_AST.PatWild 
                 |FStar_Parser_AST.PatOp _|FStar_Parser_AST.PatConst _ -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar _
                 |FStar_Parser_AST.PatName _|FStar_Parser_AST.PatTvar _ -> ()
               | FStar_Parser_AST.PatList ps
                 |FStar_Parser_AST.PatOr ps|FStar_Parser_AST.PatTuple (ps,_)
                   -> collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____1090  ->
                        match uu____1090 with
                        | (uu____1093,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             
             and collect_branches bs = FStar_List.iter collect_branch bs
             
             and collect_branch uu____1108 =
               match uu____1108 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2)
              in
             let uu____1120 = FStar_Parser_Driver.parse_file filename  in
             match uu____1120 with
             | (ast,uu____1128) -> (collect_file ast; FStar_ST.read deps))
  
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let uu____1157 =
     let uu____1158 =
       let uu____1159 =
         let uu____1160 =
           let uu____1162 =
             let uu____1164 = FStar_Util.smap_keys graph  in
             FStar_List.unique uu____1164  in
           FStar_List.collect
             (fun k  ->
                let deps =
                  let uu____1172 =
                    let uu____1176 = FStar_Util.smap_try_find graph k  in
                    FStar_Util.must uu____1176  in
                  Prims.fst uu____1172  in
                let r s = FStar_Util.replace_char s '.' '_'  in
                FStar_List.map
                  (fun dep1  ->
                     FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
             uu____1162
            in
         FStar_String.concat "\n" uu____1160  in
       Prims.strcat uu____1159 "\n}\n"  in
     Prims.strcat "digraph {\n" uu____1158  in
   FStar_Util.write_file "dep.graph" uu____1157)
  
let collect :
  verify_mode ->
    Prims.string Prims.list ->
      ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string
        Prims.list * (Prims.string Prims.list * color) FStar_Util.smap)
  =
  fun verify_mode  ->
    fun filenames  ->
      let graph = FStar_Util.smap_create (Prims.parse_int "41")  in
      let verify_flags =
        let uu____1238 = FStar_Options.verify_module ()  in
        FStar_List.map
          (fun f  ->
             let uu____1244 = FStar_Util.mk_ref false  in (f, uu____1244))
          uu____1238
         in
      let m = build_map filenames  in
      let collect_one1 = collect_one verify_flags verify_mode  in
      let partial_discovery =
        let uu____1260 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ())  in
        Prims.op_Negation uu____1260  in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____1271 =
          let uu____1272 = FStar_Util.smap_try_find graph key  in
          uu____1272 = None  in
        if uu____1271
        then
          let uu____1287 =
            let uu____1292 = FStar_Util.smap_try_find m key  in
            FStar_Util.must uu____1292  in
          match uu____1287 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | None  -> []  in
              let impl_deps =
                match (impl, intf) with
                | (Some impl1,Some uu____1322) when interface_only -> []
                | (Some impl1,uu____1326) ->
                    collect_one1 is_user_provided_filename m impl1
                | (None ,uu____1330) -> []  in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps)  in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else ()  in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f  in
        let uu____1347 = is_interface f  in
        if uu____1347
        then discover_one true true m1
        else discover_one true false m1  in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph  in
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec discover cycle key =
         let uu____1373 =
           let uu____1377 = FStar_Util.smap_try_find graph key  in
           FStar_Util.must uu____1377  in
         match uu____1373 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1
                     "Warning: recursive dependency on module %s\n" key;
                   FStar_Util.print1 "The cycle is: %s \n"
                     (FStar_String.concat " -> " cycle);
                   print_graph immediate_graph;
                   FStar_Util.print_string "\n";
                   FStar_All.exit (Prims.parse_int "1"))
              | Black  -> direct_deps
              | White  ->
                  (FStar_Util.smap_add graph key (direct_deps, Gray);
                   (let all_deps =
                      let uu____1406 =
                        let uu____1408 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____1413 = discover (key :: cycle) dep1
                                  in
                               dep1 :: uu____1413) direct_deps
                           in
                        FStar_List.flatten uu____1408  in
                      FStar_List.unique uu____1406  in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____1421 =
                       let uu____1423 = FStar_ST.read topologically_sorted
                          in
                       key :: uu____1423  in
                     FStar_ST.write topologically_sorted uu____1421);
                    all_deps)))
          in
       let discover1 = discover []  in
       let must_find k =
         let uu____1440 =
           let uu____1445 = FStar_Util.smap_try_find m k  in
           FStar_Util.must uu____1445  in
         match uu____1440 with
         | (Some intf,Some impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____1464 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____1466 = lowercase_module_name f  in
                       uu____1466 = k) filenames
                   in
                Prims.op_Negation uu____1464)
             -> [intf; impl]
         | (Some intf,Some impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____1472 = lowercase_module_name f  in
                     uu____1472 = k)) filenames
             -> [intf; impl]
         | (Some intf,uu____1474) -> [intf]
         | (None ,Some impl) -> [impl]
         | (None ,None ) -> []  in
       let must_find_r f =
         let uu____1488 = must_find f  in FStar_List.rev uu____1488  in
       let by_target =
         let uu____1495 =
           let uu____1497 = FStar_Util.smap_keys graph  in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____1497
            in
         FStar_List.collect
           (fun k  ->
              let as_list = must_find k  in
              let is_interleaved =
                (FStar_List.length as_list) = (Prims.parse_int "2")  in
              FStar_List.map
                (fun f  ->
                   let should_append_fsti =
                     (is_implementation f) && is_interleaved  in
                   let suffix =
                     if should_append_fsti then [Prims.strcat f "i"] else []
                      in
                   let k1 = lowercase_module_name f  in
                   let deps =
                     let uu____1525 = discover1 k1  in
                     FStar_List.rev uu____1525  in
                   let deps_as_filenames =
                     let uu____1529 = FStar_List.collect must_find deps  in
                     FStar_List.append uu____1529 suffix  in
                   (f, deps_as_filenames)) as_list) uu____1495
          in
       let topologically_sorted1 =
         let uu____1534 = FStar_ST.read topologically_sorted  in
         FStar_List.collect must_find_r uu____1534  in
       FStar_List.iter
         (fun uu____1543  ->
            match uu____1543 with
            | (m1,r) ->
                let uu____1551 =
                  (let uu____1552 = FStar_ST.read r  in
                   Prims.op_Negation uu____1552) &&
                    (let uu____1555 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____1555)
                   in
                if uu____1551
                then
                  let maybe_fst =
                    let k = FStar_String.length m1  in
                    let uu____1559 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____1563 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4")
                            in
                         uu____1563 = ".fst")
                       in
                    if uu____1559
                    then
                      let uu____1567 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4"))
                         in
                      FStar_Util.format1 " Did you mean %s ?" uu____1567
                    else ""  in
                  let uu____1572 =
                    let uu____1573 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst
                       in
                    FStar_Errors.Err uu____1573  in
                  Prims.raise uu____1572
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
  
let print_make :
  (Prims.string * Prims.string Prims.list) Prims.list -> Prims.unit =
  fun deps  ->
    FStar_List.iter
      (fun uu____1598  ->
         match uu____1598 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1
                in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
  
let print uu____1628 =
  match uu____1628 with
  | (make_deps,uu____1641,graph) ->
      let uu____1659 = FStar_Options.dep ()  in
      (match uu____1659 with
       | Some "make" -> print_make make_deps
       | Some "graph" -> print_graph graph
       | Some uu____1661 ->
           Prims.raise (FStar_Errors.Err "unknown tool for --dep\n")
       | None  -> ())
  