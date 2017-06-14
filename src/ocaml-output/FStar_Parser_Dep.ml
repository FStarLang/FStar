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
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap
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
let check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
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
             FStar_Pervasives_Native.Some uu____61
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____68 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____68 with
    | (FStar_Pervasives_Native.Some m)::uu____74 ->
        FStar_Pervasives_Native.Some m
    | uu____78 -> FStar_Pervasives_Native.None
  
let is_interface : Prims.string -> Prims.bool =
  fun f  ->
    let uu____84 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____84 = 'i'
  
let is_implementation : Prims.string -> Prims.bool =
  fun f  -> let uu____91 = is_interface f  in Prims.op_Negation uu____91 
let list_of_option uu___84_100 =
  match uu___84_100 with
  | FStar_Pervasives_Native.Some x -> [x]
  | FStar_Pervasives_Native.None  -> [] 
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
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____132 =
          let uu____133 = FStar_Util.format1 "not a valid FStar file: %s\n" f
             in
          FStar_Errors.Err uu____133  in
        raise uu____132
  
let build_map :
  Prims.string Prims.list ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Util.smap
  =
  fun filenames  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____146 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____146  in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____164 = FStar_Util.smap_try_find map1 key  in
      match uu____164 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____184 = is_interface full_path  in
          if uu____184
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____202 = is_interface full_path  in
          if uu____202
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    FStar_List.iter
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.iter
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____222 = check_and_strip_suffix f1  in
                match uu____222 with
                | FStar_Pervasives_Native.Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1  in
                    let key = FStar_String.lowercase longname  in
                    add_entry key full_path
                | FStar_Pervasives_Native.None  -> ()) files
         else
           (let uu____229 =
              let uu____230 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              FStar_Errors.Err uu____230  in
            raise uu____229)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____233 = lowercase_module_name f  in add_entry uu____233 f)
      filenames;
    map1
  
let enter_namespace : map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false  in
        let prefix2 = Prims.strcat prefix1 "."  in
        (let uu____248 =
           let uu____250 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____250  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____270 = FStar_Util.smap_try_find original_map k  in
                  FStar_Util.must uu____270  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.write found true)
              else ()) uu____248);
        FStar_ST.read found
  
let string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____306 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____306 suffix  in
      FStar_String.concat "." names
  
let lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____315 = string_of_lid l last1  in
      FStar_String.lowercase uu____315
  
let namespace_of_lid : FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____319 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____319
  
let check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____328 =
        let uu____329 =
          let uu____330 =
            let uu____331 =
              let uu____333 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____333  in
            FStar_Util.must uu____331  in
          FStar_String.lowercase uu____330  in
        uu____329 <> k'  in
      if uu____328
      then
        let uu____334 = string_of_lid lid true  in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____334 filename
      else ()
  
exception Exit 
let uu___is_Exit : Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____339 -> false 
let hard_coded_dependencies : Prims.string -> FStar_Ident.lident Prims.list =
  fun filename  ->
    let filename1 = FStar_Util.basename filename  in
    let corelibs =
      let uu____347 = FStar_Options.prims_basename ()  in
      let uu____348 =
        let uu____350 = FStar_Options.pervasives_basename ()  in
        let uu____351 =
          let uu____353 = FStar_Options.pervasives_native_basename ()  in
          [uu____353]  in
        uu____350 :: uu____351  in
      uu____347 :: uu____348  in
    if FStar_List.mem filename1 corelibs
    then []
    else
      [FStar_Parser_Const.fstar_ns_lid;
      FStar_Parser_Const.prims_lid;
      FStar_Parser_Const.pervasives_lid]
  
let collect_one :
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
            let deps = FStar_Util.mk_ref []  in
            let add_dep d =
              let uu____390 =
                let uu____391 =
                  let uu____392 = FStar_ST.read deps  in
                  FStar_List.existsML (fun d'  -> d' = d) uu____392  in
                Prims.op_Negation uu____391  in
              if uu____390
              then
                let uu____398 =
                  let uu____400 = FStar_ST.read deps  in d :: uu____400  in
                FStar_ST.write deps uu____398
              else ()  in
            let working_map = FStar_Util.smap_copy original_map  in
            let record_open let_open lid =
              let key = lowercase_join_longident lid true  in
              let uu____427 = FStar_Util.smap_try_find working_map key  in
              match uu____427 with
              | FStar_Pervasives_Native.Some pair ->
                  FStar_List.iter
                    (fun f  ->
                       let uu____447 = lowercase_module_name f  in
                       add_dep uu____447) (list_of_pair pair)
              | FStar_Pervasives_Native.None  ->
                  let r = enter_namespace original_map working_map key  in
                  if Prims.op_Negation r
                  then
                    (if let_open
                     then
                       raise
                         (FStar_Errors.Err
                            "let-open only supported for modules, not namespaces")
                     else
                       (let uu____454 = string_of_lid lid true  in
                        FStar_Util.print1_warning
                          "Warning: no modules in namespace %s and no file with that name either\n"
                          uu____454))
                  else ()
               in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident)
                 in
              let alias = lowercase_join_longident lid true  in
              let uu____465 = FStar_Util.smap_try_find original_map alias  in
              match uu____465 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____492 =
                    let uu____493 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias
                       in
                    FStar_Errors.Err uu____493  in
                  raise uu____492
               in
            let record_lid lid =
              let try_key key =
                let uu____502 = FStar_Util.smap_try_find working_map key  in
                match uu____502 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____522 = lowercase_module_name f  in
                         add_dep uu____522) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____527 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ())
                       in
                    if uu____527
                    then
                      let uu____531 =
                        FStar_Range.string_of_range
                          (FStar_Ident.range_of_lid lid)
                         in
                      let uu____532 = string_of_lid lid false  in
                      FStar_Util.print2_warning
                        "%s (Warning): unbound module reference %s\n"
                        uu____531 uu____532
                    else ()
                 in
              let uu____535 = lowercase_join_longident lid false  in
              try_key uu____535  in
            let auto_open = hard_coded_dependencies filename  in
            FStar_List.iter (record_open false) auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0")  in
             let rec collect_fragment uu___85_610 =
               match uu___85_610 with
               | FStar_Util.Inl file -> collect_file file
               | FStar_Util.Inr decls -> collect_decls decls
             
             and collect_file uu___86_623 =
               match uu___86_623 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.print1_warning
                      "Warning: file %s does not respect the one module per file convention\n"
                      filename;
                    FStar_List.iter collect_module modules)
             
             and collect_module uu___87_629 =
               match uu___87_629 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____639 =
                         let uu____640 = namespace_of_lid lid  in
                         enter_namespace original_map working_map uu____640
                          in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____643 = string_of_lid lid true  in
                         FStar_Options.add_verify_module uu____643
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____644 = string_of_lid lid true  in
                           FStar_Options.add_verify_module uu____644
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____649  ->
                              match uu____649 with
                              | (m,r) ->
                                  let uu____657 =
                                    let uu____658 =
                                      let uu____659 = string_of_lid lid true
                                         in
                                      FStar_String.lowercase uu____659  in
                                    (FStar_String.lowercase m) = uu____658
                                     in
                                  if uu____657
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____665) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____673 =
                         let uu____674 = namespace_of_lid lid  in
                         enter_namespace original_map working_map uu____674
                          in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____677 = string_of_lid lid true  in
                         FStar_Options.add_verify_module uu____677
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____678 = string_of_lid lid true  in
                           FStar_Options.add_verify_module uu____678
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____683  ->
                              match uu____683 with
                              | (m,r) ->
                                  let uu____691 =
                                    let uu____692 =
                                      let uu____693 = string_of_lid lid true
                                         in
                                      FStar_String.lowercase uu____693  in
                                    (FStar_String.lowercase m) = uu____692
                                     in
                                  if uu____691
                                  then FStar_ST.write r true
                                  else ()) verify_flags);
                    collect_decls decls)
             
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             
             and collect_decl uu___88_701 =
               match uu___88_701 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____707 = lowercase_join_longident lid true  in
                     add_dep uu____707);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____708,patterms) ->
                   FStar_List.iter
                     (fun uu____718  ->
                        match uu____718 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____725,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____727;
                     FStar_Parser_AST.mdest = uu____728;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____730;
                     FStar_Parser_AST.mdest = uu____731;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____733,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____735;
                     FStar_Parser_AST.mdest = uu____736;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____740,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____755  ->
                          match uu____755 with | (x,doc1) -> x) ts
                      in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____763,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____768 -> ()
               | FStar_Parser_AST.Pragma uu____769 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____775 =
                       let uu____776 = FStar_ST.read num_of_toplevelmods  in
                       uu____776 > (Prims.parse_int "1")  in
                     if uu____775
                     then
                       let uu____779 =
                         let uu____780 =
                           let uu____781 = string_of_lid lid true  in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____781
                            in
                         FStar_Errors.Err uu____780  in
                       raise uu____779
                     else ()))
             
             and collect_tycon uu___89_783 =
               match uu___89_783 with
               | FStar_Parser_AST.TyconAbstract (uu____784,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____792,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____802,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____826  ->
                         match uu____826 with
                         | (uu____831,t,uu____833) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____836,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____866  ->
                         match uu____866 with
                         | (uu____873,t,uu____875,uu____876) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             
             and collect_effect_decl uu___90_881 =
               match uu___90_881 with
               | FStar_Parser_AST.DefineEffect (uu____882,binders,t,decls) ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____892,binders,t) ->
                   (collect_binders binders; collect_term t)
             
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             
             and collect_binder uu___91_900 =
               match uu___91_900 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____901,t);
                   FStar_Parser_AST.brange = uu____903;
                   FStar_Parser_AST.blevel = uu____904;
                   FStar_Parser_AST.aqual = uu____905;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____906,t);
                   FStar_Parser_AST.brange = uu____908;
                   FStar_Parser_AST.blevel = uu____909;
                   FStar_Parser_AST.aqual = uu____910;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____912;
                   FStar_Parser_AST.blevel = uu____913;
                   FStar_Parser_AST.aqual = uu____914;_} -> collect_term t
               | uu____915 -> ()
             
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             
             and collect_constant uu___92_917 =
               match uu___92_917 with
               | FStar_Const.Const_int
                   (uu____918,FStar_Pervasives_Native.Some
                    (signedness,width))
                   ->
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
                   let uu____928 = FStar_Util.format2 "fstar.%sint%s" u w  in
                   add_dep uu____928
               | uu____929 -> ()
             
             and collect_term' uu___93_930 =
               match uu___93_930 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____937 =
                         let uu____938 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange
                            in
                         FStar_Parser_AST.Name uu____938  in
                       collect_term' uu____937)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____940 -> ()
               | FStar_Parser_AST.Uvar uu____941 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____944) -> record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____963  ->
                         match uu____963 with
                         | (t,uu____967) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____975) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____977,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____989  ->
                         match uu____989 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____998,t1,t2) ->
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
                      (fun uu____1059  ->
                         match uu____1059 with
                         | (uu____1062,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____1065) -> collect_term t
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
               | FStar_Parser_AST.NamedTyp (uu____1103,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____1106,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____1109) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____1113) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____1117,uu____1118) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             
             and collect_pattern' uu___94_1124 =
               match uu___94_1124 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____1125 -> ()
               | FStar_Parser_AST.PatConst uu____1126 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____1132 -> ()
               | FStar_Parser_AST.PatName uu____1136 -> ()
               | FStar_Parser_AST.PatTvar uu____1137 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____1146) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____1155  ->
                        match uu____1155 with
                        | (uu____1158,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             
             and collect_branches bs = FStar_List.iter collect_branch bs
             
             and collect_branch uu____1173 =
               match uu____1173 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2)
              in
             let uu____1185 = FStar_Parser_Driver.parse_file filename  in
             match uu____1185 with
             | (ast,uu____1193) -> (collect_file ast; FStar_ST.read deps))
  
let print_graph graph =
  FStar_Util.print_endline
    "A DOT-format graph has been dumped in the current directory as dep.graph";
  FStar_Util.print_endline
    "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  (let uu____1222 =
     let uu____1223 =
       let uu____1224 =
         let uu____1225 =
           let uu____1227 =
             let uu____1229 = FStar_Util.smap_keys graph  in
             FStar_List.unique uu____1229  in
           FStar_List.collect
             (fun k  ->
                let deps =
                  let uu____1237 =
                    let uu____1241 = FStar_Util.smap_try_find graph k  in
                    FStar_Util.must uu____1241  in
                  FStar_Pervasives_Native.fst uu____1237  in
                let r s = FStar_Util.replace_char s '.' '_'  in
                FStar_List.map
                  (fun dep1  ->
                     FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
             uu____1227
            in
         FStar_String.concat "\n" uu____1225  in
       Prims.strcat uu____1224 "\n}\n"  in
     Prims.strcat "digraph {\n" uu____1223  in
   FStar_Util.write_file "dep.graph" uu____1222)
  
let collect :
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
      let graph = FStar_Util.smap_create (Prims.parse_int "41")  in
      let verify_flags =
        let uu____1303 = FStar_Options.verify_module ()  in
        FStar_List.map
          (fun f  ->
             let uu____1309 = FStar_Util.mk_ref false  in (f, uu____1309))
          uu____1303
         in
      let partial_discovery =
        let uu____1316 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ())  in
        Prims.op_Negation uu____1316  in
      let m = build_map filenames  in
      let file_names_of_key k =
        let uu____1322 =
          let uu____1327 = FStar_Util.smap_try_find m k  in
          FStar_Util.must uu____1327  in
        match uu____1322 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____1358) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j))
         in
      let collect_one1 = collect_one verify_flags verify_mode  in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____1384 =
          let uu____1385 = FStar_Util.smap_try_find graph key  in
          uu____1385 = FStar_Pervasives_Native.None  in
        if uu____1384
        then
          let uu____1400 =
            let uu____1405 = FStar_Util.smap_try_find m key  in
            FStar_Util.must uu____1405  in
          match uu____1400 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> []  in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____1435) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____1439) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____1443) -> []  in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps)  in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else ()  in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f  in
        let interface_only =
          (is_interface f) &&
            (let uu____1461 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____1463 = lowercase_module_name f1  in
                     uu____1463 = m1) && (is_implementation f1)) filenames
                in
             Prims.op_Negation uu____1461)
           in
        discover_one true interface_only m1  in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph  in
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec discover cycle key =
         let uu____1488 =
           let uu____1492 = FStar_Util.smap_try_find graph key  in
           FStar_Util.must uu____1492  in
         match uu____1488 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1
                     "Warning: recursive dependency on module %s\n" key;
                   (let cycle1 =
                      FStar_All.pipe_right cycle
                        (FStar_List.map file_names_of_key)
                       in
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
                      let uu____1525 =
                        let uu____1527 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____1532 = discover (key :: cycle) dep1
                                  in
                               dep1 :: uu____1532) direct_deps
                           in
                        FStar_List.flatten uu____1527  in
                      FStar_List.unique uu____1525  in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____1540 =
                       let uu____1542 = FStar_ST.read topologically_sorted
                          in
                       key :: uu____1542  in
                     FStar_ST.write topologically_sorted uu____1540);
                    all_deps)))
          in
       let discover1 = discover []  in
       let must_find k =
         let uu____1559 =
           let uu____1564 = FStar_Util.smap_try_find m k  in
           FStar_Util.must uu____1564  in
         match uu____1559 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____1583 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____1585 = lowercase_module_name f  in
                       uu____1585 = k) filenames
                   in
                Prims.op_Negation uu____1583)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____1591 = lowercase_module_name f  in
                     uu____1591 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____1593) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             []
          in
       let must_find_r f =
         let uu____1607 = must_find f  in FStar_List.rev uu____1607  in
       let by_target =
         let uu____1614 =
           let uu____1616 = FStar_Util.smap_keys graph  in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____1616
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
                   let k1 = lowercase_module_name f  in
                   let suffix =
                     let uu____1640 =
                       let uu____1645 = FStar_Util.smap_try_find m k1  in
                       FStar_Util.must uu____1645  in
                     match uu____1640 with
                     | (FStar_Pervasives_Native.Some intf,uu____1661) when
                         should_append_fsti -> [intf]
                     | uu____1665 -> []  in
                   let deps =
                     let uu____1672 = discover1 k1  in
                     FStar_List.rev uu____1672  in
                   let deps_as_filenames =
                     let uu____1676 = FStar_List.collect must_find deps  in
                     FStar_List.append uu____1676 suffix  in
                   (f, deps_as_filenames)) as_list) uu____1614
          in
       let topologically_sorted1 =
         let uu____1681 = FStar_ST.read topologically_sorted  in
         FStar_List.collect must_find_r uu____1681  in
       FStar_List.iter
         (fun uu____1690  ->
            match uu____1690 with
            | (m1,r) ->
                let uu____1698 =
                  (let uu____1699 = FStar_ST.read r  in
                   Prims.op_Negation uu____1699) &&
                    (let uu____1702 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____1702)
                   in
                if uu____1698
                then
                  let maybe_fst =
                    let k = FStar_String.length m1  in
                    let uu____1706 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____1710 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4")
                            in
                         uu____1710 = ".fst")
                       in
                    if uu____1706
                    then
                      let uu____1714 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4"))
                         in
                      FStar_Util.format1 " Did you mean %s ?" uu____1714
                    else ""  in
                  let uu____1719 =
                    let uu____1720 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst
                       in
                    FStar_Errors.Err uu____1720  in
                  raise uu____1719
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
  
let print_make :
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____1745  ->
         match uu____1745 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1
                in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
  
let print uu____1775 =
  match uu____1775 with
  | (make_deps,uu____1788,graph) ->
      let uu____1806 = FStar_Options.dep ()  in
      (match uu____1806 with
       | FStar_Pervasives_Native.Some "make" -> print_make make_deps
       | FStar_Pervasives_Native.Some "graph" -> print_graph graph
       | FStar_Pervasives_Native.Some uu____1808 ->
           raise (FStar_Errors.Err "unknown tool for --dep\n")
       | FStar_Pervasives_Native.None  -> ())
  