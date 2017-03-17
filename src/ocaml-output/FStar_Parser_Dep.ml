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
               (let _0_842 = FStar_String.substring f (l - lext) lext  in
                _0_842 = ext)
              in
           match uu____46 with
           | true  ->
               Some
                 (FStar_String.substring f (Prims.parse_int "0") (l - lext))
           | uu____65 -> None) suffixes
       in
    let uu____66 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____66 with | (Some m)::uu____72 -> Some m | uu____76 -> None
  
let is_interface : Prims.string -> Prims.bool =
  fun f  ->
    let _0_843 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    _0_843 = 'i'
  
let is_implementation : Prims.string -> Prims.bool =
  fun f  -> Prims.op_Negation (is_interface f) 
let list_of_option uu___129_96 =
  match uu___129_96 with | Some x -> [x] | None  -> [] 
let list_of_pair uu____110 =
  match uu____110 with
  | (intf,impl) ->
      FStar_List.append (list_of_option intf) (list_of_option impl)
  
let lowercase_module_name : Prims.string -> Prims.string =
  fun f  ->
    let uu____124 = check_and_strip_suffix (FStar_Util.basename f)  in
    match uu____124 with
    | Some longname -> FStar_String.lowercase longname
    | None  ->
        Prims.raise
          (FStar_Errors.Err
             (FStar_Util.format1 "not a valid FStar file: %s\n" f))
  
let try_convert_file_name_to_windows : Prims.string -> Prims.string =
  fun s  ->
    try
      let uu____131 = FStar_Util.run_proc "which" "cygpath" ""  in
      match uu____131 with
      | (uu____135,t_out,uu____137) ->
          (match Prims.op_Negation
                   ((FStar_Util.trim_string t_out) = "/usr/bin/cygpath")
           with
           | true  -> s
           | uu____138 ->
               let uu____139 =
                 FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) ""  in
               (match uu____139 with
                | (uu____143,t_out,uu____145) -> FStar_Util.trim_string t_out))
    with | uu____147 -> s
  
let build_map :
  Prims.string Prims.list ->
    (Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap
  =
  fun filenames  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories =
      FStar_List.map try_convert_file_name_to_windows include_directories  in
    let include_directories =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories = FStar_List.unique include_directories  in
    let cwd = FStar_Util.normalize_file_path (FStar_Util.getcwd ())  in
    let map = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____179 = FStar_Util.smap_try_find map key  in
      match uu____179 with
      | Some (intf,impl) ->
          let uu____199 = is_interface full_path  in
          (match uu____199 with
           | true  -> FStar_Util.smap_add map key ((Some full_path), impl)
           | uu____206 ->
               FStar_Util.smap_add map key (intf, (Some full_path)))
      | None  ->
          let uu____217 = is_interface full_path  in
          (match uu____217 with
           | true  -> FStar_Util.smap_add map key ((Some full_path), None)
           | uu____224 ->
               FStar_Util.smap_add map key (None, (Some full_path)))
       in
    FStar_List.iter
      (fun d  ->
         match FStar_Util.file_exists d with
         | true  ->
             let files = FStar_Util.readdir d  in
             FStar_List.iter
               (fun f  ->
                  let f = FStar_Util.basename f  in
                  let uu____237 = check_and_strip_suffix f  in
                  match uu____237 with
                  | Some longname ->
                      let full_path =
                        match d = cwd with
                        | true  -> f
                        | uu____241 -> FStar_Util.join_paths d f  in
                      let key = FStar_String.lowercase longname  in
                      add_entry key full_path
                  | None  -> ()) files
         | uu____243 ->
             Prims.raise
               (FStar_Errors.Err
                  (FStar_Util.format1 "not a valid include directory: %s\n" d)))
      include_directories;
    FStar_List.iter
      (fun f  -> let _0_844 = lowercase_module_name f  in add_entry _0_844 f)
      filenames;
    map
  
let enter_namespace : map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix  ->
        let found = FStar_Util.mk_ref false  in
        let prefix = Prims.strcat prefix "."  in
        (let _0_845 = FStar_List.unique (FStar_Util.smap_keys original_map)
            in
         FStar_List.iter
           (fun k  ->
              match FStar_Util.starts_with k prefix with
              | true  ->
                  let suffix =
                    FStar_String.substring k (FStar_String.length prefix)
                      ((FStar_String.length k) - (FStar_String.length prefix))
                     in
                  let filename =
                    FStar_Util.must (FStar_Util.smap_try_find original_map k)
                     in
                  (FStar_Util.smap_add working_map suffix filename;
                   FStar_ST.write found true)
              | uu____289 -> ()) _0_845);
        FStar_ST.read found
  
let string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        match last with
        | true  -> [(l.FStar_Ident.ident).FStar_Ident.idText]
        | uu____305 -> []  in
      let names =
        let _0_846 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append _0_846 suffix  in
      FStar_String.concat "." names
  
let lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  -> fun last  -> FStar_String.lowercase (string_of_lid l last) 
let check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____322 =
        let _0_847 =
          FStar_String.lowercase
            (FStar_Util.must
               (check_and_strip_suffix (FStar_Util.basename filename)))
           in
        _0_847 <> k'  in
      match uu____322 with
      | true  ->
          let _0_849 =
            let _0_848 = string_of_lid lid true  in [_0_848; filename]  in
          FStar_Util.fprint FStar_Util.stderr
            "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
            _0_849
      | uu____323 -> ()
  
exception Exit 
let uu___is_Exit : Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____327 -> false 
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
              let uu____362 =
                Prims.op_Negation
                  (let _0_850 = FStar_ST.read deps  in
                   FStar_List.existsb (fun d'  -> d' = d) _0_850)
                 in
              match uu____362 with
              | true  ->
                  let _0_852 =
                    let _0_851 = FStar_ST.read deps  in d :: _0_851  in
                  FStar_ST.write deps _0_852
              | uu____373 -> ()  in
            let working_map = FStar_Util.smap_copy original_map  in
            let record_open let_open lid =
              let key = lowercase_join_longident lid true  in
              let uu____392 = FStar_Util.smap_try_find working_map key  in
              match uu____392 with
              | Some pair ->
                  FStar_List.iter
                    (fun f  ->
                       let uu____428 = lowercase_module_name f in
                       add_dep uu____428) (list_of_pair pair)
              | None  ->
                  let r = enter_namespace original_map working_map key  in
                  (match Prims.op_Negation r with
                   | true  ->
                       (match let_open with
                        | true  ->
                            Prims.raise
                              (FStar_Errors.Err
                                 "let-open only supported for modules, not namespaces")
                        | uu____417 ->
                            let _0_854 =
                              let _0_853 = string_of_lid lid true  in
                              [_0_853]  in
                            FStar_Util.fprint FStar_Util.stderr
                              "Warning: no modules in namespace %s and no file with that name either\n"
                              _0_854)
                   | uu____418 -> ())
               in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident)
                 in
              let alias = lowercase_join_longident lid true  in
              let uu____428 = FStar_Util.smap_try_find original_map alias  in
              match uu____428 with
              | Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | None  ->
                  Prims.raise
                    (FStar_Errors.Err
                       (FStar_Util.format1
                          "module not found in search path: %s\n" alias))
               in
            let record_lid lid =
              let try_key key =
                let uu____463 = FStar_Util.smap_try_find working_map key  in
                match uu____463 with
                | Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____505 = lowercase_module_name f in
                         add_dep uu____505) (list_of_pair pair)
                | None  ->
                    let uu____510 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ())
                       in
                    (match uu____487 with
                     | true  ->
                         let _0_856 =
                           let _0_855 = string_of_lid lid false  in [_0_855]
                            in
                         FStar_Util.fprint FStar_Util.stderr
                           "Warning: unbound module reference %s\n" _0_856
                     | uu____491 -> ())
                 in
              try_key (lowercase_join_longident lid false)  in
            let auto_open =
              let uu____495 =
                let _0_857 = FStar_Util.basename filename  in
                _0_857 = "prims.fst"  in
              match uu____495 with
              | true  -> []
              | uu____497 ->
                  [FStar_Syntax_Const.fstar_ns_lid;
                  FStar_Syntax_Const.prims_lid]
               in
            FStar_List.iter (record_open false) auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0")  in
             let rec collect_fragment uu___130_570 =
               match uu___130_570 with
               | FStar_Util.Inl file -> collect_file file
               | FStar_Util.Inr decls -> collect_decls decls
             
             and collect_file uu___131_583 =
               match uu___131_583 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.fprint FStar_Util.stderr
                      "Warning: file %s does not respect the one module per file convention\n"
                      [filename];
                    FStar_List.iter collect_module modules)
             
             and collect_module uu___132_589 =
               match uu___132_589 with
               | FStar_Parser_AST.Module (lid,decls)
                 |FStar_Parser_AST.Interface (lid,decls,_) ->
                   (check_module_declaration_against_filename lid filename;
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____628 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____628
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____629 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____629
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____634  ->
                              match uu____634 with
                              | (m,r) ->
                                  let uu____611 =
                                    let _0_858 =
                                      FStar_String.lowercase
                                        (string_of_lid lid true)
                                       in
                                    (FStar_String.lowercase m) = _0_858  in
                                  (match uu____611 with
                                   | true  -> FStar_ST.write r true
                                   | uu____614 -> ())) verify_flags);
                    collect_decls decls)
             
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             
             and collect_decl uu___133_619 =
               match uu___133_619 with
               | FStar_Parser_AST.Include lid|FStar_Parser_AST.Open lid ->
                   record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____657 = lowercase_join_longident lid true in
                     add_dep uu____657);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____658,patterms) ->
                   FStar_List.iter
                     (fun uu____668  ->
                        match uu____668 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t
                 |FStar_Parser_AST.Assume (_,t)
                  |FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = _;
                     FStar_Parser_AST.mdest = _;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   |FStar_Parser_AST.SubEffect
                    { FStar_Parser_AST.msource = _;
                      FStar_Parser_AST.mdest = _;
                      FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                        t;_}|FStar_Parser_AST.Val (_,t)
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____681;
                     FStar_Parser_AST.mdest = uu____682;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____686,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____667  -> match uu____667 with | (x,doc) -> x)
                       ts
                      in
                   FStar_List.iter collect_tycon ts
               | FStar_Parser_AST.Exception (uu____675,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc _|FStar_Parser_AST.Pragma _ -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____687 =
                       let _0_859 = FStar_ST.read num_of_toplevelmods  in
                       _0_859 > (Prims.parse_int "1")  in
                     match uu____687 with
                     | true  ->
                         Prims.raise
                           (FStar_Errors.Err
                              (let _0_860 = string_of_lid lid true  in
                               FStar_Util.format1
                                 "Automatic dependency analysis demands one module per file (module %s not supported)"
                                 _0_860))
                     | uu____690 -> ()))
             
             and collect_tycon uu___134_691 =
               match uu___134_691 with
               | FStar_Parser_AST.TyconAbstract (uu____692,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____738,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____748,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____772  ->
                         match uu____772 with
                         | (uu____777,t,uu____779) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____782,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____812  ->
                         match uu____812 with
                         | (uu____819,t,uu____821,uu____822) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             
             and collect_effect_decl uu___135_789 =
               match uu___135_789 with
               | FStar_Parser_AST.DefineEffect
                   (uu____790,binders,t,decls,actions) ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____838,binders,t) ->
                   (collect_binders binders; collect_term t)
             
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             
             and collect_binder uu___136_812 =
               match uu___136_812 with
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
               | uu____825 -> ()
             
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             
             and collect_constant uu___137_827 =
               match uu___137_827 with
               | FStar_Const.Const_int (uu____828,Some (signedness,width)) ->
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
                   add_dep (FStar_Util.format2 "fstar.%sint%s" u w)
               | uu____838 -> ()
             
             and collect_term' uu___138_839 =
               match uu___138_839 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if s = "@"
                    then
                      (let uu____881 =
                         let uu____882 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____882 in
                       collect_term' uu____881)
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
                      (fun uu____904  ->
                         match uu____904 with
                         | (t,uu____908) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____916) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____918,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____930  ->
                         match uu____930 with
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
               | FStar_Parser_AST.Ascribed (t1,t2,None ) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Ascribed (t1,t2,Some tac) ->
                   (collect_term t1; collect_term t2; collect_term tac)
               | FStar_Parser_AST.Record (t,idterms) ->
                   (FStar_Util.iter_opt t collect_term;
                    FStar_List.iter
                      (fun uu____993  ->
                         match uu____993 with
                         | (uu____996,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____999) -> collect_term t
               | FStar_Parser_AST.Product (binders,t)|FStar_Parser_AST.Sum
                 (binders,t) -> (collect_binders binders; collect_term t)
               | FStar_Parser_AST.QForall (binders,ts,t)
                 |FStar_Parser_AST.QExists (binders,ts,t) ->
                   (collect_binders binders;
                    FStar_List.iter (FStar_List.iter collect_term) ts;
                    collect_term t)
               | FStar_Parser_AST.Refine (binder,t) ->
                   (collect_binder binder; collect_term t)
               | FStar_Parser_AST.NamedTyp (uu____1028,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (_,t)
                 |FStar_Parser_AST.Requires (t,_)
                  |FStar_Parser_AST.Ensures (t,_)|FStar_Parser_AST.Labeled
                   (t,_,_) -> collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             
             and collect_pattern' uu___139_1000 =
               match uu___139_1000 with
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
                     (fun uu____1067  ->
                        match uu____1067 with
                        | (uu____1070,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             
             and collect_branches bs = FStar_List.iter collect_branch bs
             
             and collect_branch uu____1041 =
               match uu____1041 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2)
              in
             let uu____1053 = FStar_Parser_Driver.parse_file filename  in
             match uu____1053 with
             | (ast,uu____1061) -> (collect_file ast; FStar_ST.read deps))
  
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let _0_865 =
     let _0_864 =
       let _0_863 =
         let _0_862 =
           let _0_861 = FStar_List.unique (FStar_Util.smap_keys graph)  in
           FStar_List.collect
             (fun k  ->
                let deps =
                  Prims.fst
                    (FStar_Util.must (FStar_Util.smap_try_find graph k))
                   in
                let r s = FStar_Util.replace_char s '.' '_'  in
                FStar_List.map
                  (fun dep  -> FStar_Util.format2 "  %s -> %s" (r k) (r dep))
                  deps) _0_861
            in
         FStar_String.concat "\n" _0_862  in
       Prims.strcat _0_863 "\n}\n"  in
     Prims.strcat "digraph {\n" _0_864  in
   FStar_Util.write_file "dep.graph" _0_865)
  
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
        let _0_867 = FStar_Options.verify_module ()  in
        FStar_List.map
          (fun f  -> let _0_866 = FStar_Util.mk_ref false  in (f, _0_866))
          _0_867
         in
      let m = build_map filenames  in
      let collect_one = collect_one verify_flags verify_mode  in
      let partial_discovery =
        Prims.op_Negation
          ((FStar_Options.verify_all ()) || (FStar_Options.extract_all ()))
         in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____1180 =
          let _0_868 = FStar_Util.smap_try_find graph key  in _0_868 = None
           in
        match uu____1180 with
        | true  ->
            let uu____1191 = FStar_Util.must (FStar_Util.smap_try_find m key)
               in
            (match uu____1191 with
             | (intf,impl) ->
                 let intf_deps =
                   match intf with
                   | Some intf ->
                       collect_one is_user_provided_filename m intf
                   | None  -> []  in
                 let impl_deps =
                   match (impl, intf) with
                   | (Some impl,Some uu____1220) when interface_only -> []
                   | (Some impl,uu____1224) ->
                       collect_one is_user_provided_filename m impl
                   | (None ,uu____1228) -> []  in
                 let deps =
                   FStar_List.unique (FStar_List.append impl_deps intf_deps)
                    in
                 (FStar_Util.smap_add graph key (deps, White);
                  FStar_List.iter (discover_one false partial_discovery) deps))
        | uu____1239 -> ()  in
      let discover_command_line_argument f =
        let m = lowercase_module_name f  in
        let uu____1245 = is_interface f  in
        match uu____1245 with
        | true  -> discover_one true true m
        | uu____1246 -> discover_one true false m  in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph  in
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec discover cycle key =
         let uu____1271 =
           FStar_Util.must (FStar_Util.smap_try_find graph key)  in
         match uu____1271 with
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
                      FStar_List.unique
                        (FStar_List.flatten
                           (FStar_List.map
                              (fun dep  ->
                                 let _0_869 = discover (key :: cycle) dep  in
                                 dep :: _0_869) direct_deps))
                       in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let _0_871 =
                       let _0_870 = FStar_ST.read topologically_sorted  in
                       key :: _0_870  in
                     FStar_ST.write topologically_sorted _0_871);
                    all_deps)))
          in
       let discover = discover []  in
       let must_find k =
         let uu____1322 = FStar_Util.must (FStar_Util.smap_try_find m k)  in
         match uu____1322 with
         | (Some intf,Some impl) when
             (Prims.op_Negation partial_discovery) &&
               (Prims.op_Negation
                  (FStar_List.existsML
                     (fun f  ->
                        let _0_872 = lowercase_module_name f  in _0_872 = k)
                     filenames))
             -> [intf; impl]
         | (Some intf,Some impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let _0_873 = lowercase_module_name f  in _0_873 = k))
               filenames
             -> [intf; impl]
         | (Some intf,uu____1451) -> [intf]
         | (None ,Some impl) -> [impl]
         | (None ,None ) -> []  in
       let must_find_r f = FStar_List.rev (must_find f)  in
       let by_target =
         let _0_875 = FStar_Util.smap_keys graph  in
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
                     match should_append_fsti with
                     | true  -> [Prims.strcat f "i"]
                     | uu____1383 -> []  in
                   let k = lowercase_module_name f  in
                   let deps = FStar_List.rev (discover k)  in
                   let deps_as_filenames =
                     let _0_874 = FStar_List.collect must_find deps  in
                     FStar_List.append _0_874 suffix  in
                   (f, deps_as_filenames)) as_list) _0_875
          in
       let topologically_sorted =
         let _0_876 = FStar_ST.read topologically_sorted  in
         FStar_List.collect must_find_r _0_876  in
       FStar_List.iter
         (fun uu____1402  ->
            match uu____1402 with
            | (m,r) ->
                let uu____1410 =
                  (Prims.op_Negation (FStar_ST.read r)) &&
                    (Prims.op_Negation (FStar_Options.interactive ()))
                   in
                (match uu____1410 with
                 | true  ->
                     let maybe_fst =
                       let k = FStar_String.length m  in
                       let uu____1416 =
                         (k > (Prims.parse_int "4")) &&
                           (let _0_877 =
                              FStar_String.substring m
                                (k - (Prims.parse_int "4"))
                                (Prims.parse_int "4")
                               in
                            _0_877 = ".fst")
                          in
                       match uu____1416 with
                       | true  ->
                           let _0_878 =
                             FStar_String.substring m (Prims.parse_int "0")
                               (k - (Prims.parse_int "4"))
                              in
                           FStar_Util.format1 " Did you mean %s ?" _0_878
                       | uu____1426 -> ""  in
                     Prims.raise
                       (FStar_Errors.Err
                          (FStar_Util.format3
                             "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                             m m maybe_fst))
                 | uu____1427 -> ())) verify_flags;
       (by_target, topologically_sorted, immediate_graph))
  
let print_make :
  (Prims.string * Prims.string Prims.list) Prims.list -> Prims.unit =
  fun deps  ->
    FStar_List.iter
      (fun uu____1575  ->
         match uu____1575 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_string s " " "\\ ") deps
                in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps))
      deps
  
let print uu____1481 =
  match uu____1481 with
  | (make_deps,uu____1494,graph) ->
      let uu____1512 = FStar_Options.dep ()  in
      (match uu____1512 with
       | Some "make" -> print_make make_deps
       | Some "graph" -> print_graph graph
       | Some uu____1638 ->
           Prims.raise (FStar_Errors.Err "unknown tool for --dep\n")
       | None  -> ())
  