open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl, FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun decls ->
    let uu____18 =
      FStar_List.partition
        (fun d ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____30 -> true
           | uu____31 -> false) decls in
    match uu____18 with
    | (top, nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____67 -> FStar_Pervasives_Native.None)
type mforest =
  | Leaf of (Prims.string, Prims.string) FStar_Pervasives_Native.tuple2 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee ->
    match projectee with | Leaf _0 -> true | uu____102 -> false
let (__proj__Leaf__item___0 :
  mforest -> (Prims.string, Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | Leaf _0 -> _0
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee ->
    match projectee with | Branch _0 -> true | uu____130 -> false
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee -> match projectee with | Branch _0 -> _0
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50")
let string_of_optiont :
  'Auu____156 'Auu____157 .
    ('Auu____156 -> 'Auu____157) ->
      'Auu____157 ->
        'Auu____156 FStar_Pervasives_Native.option -> 'Auu____157
  =
  fun f ->
    fun y ->
      fun xo ->
        match xo with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None -> y
let (string_of_fsdoco :
  (Prims.string,
    (Prims.string, Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
    Prims.string)
  =
  fun d ->
    string_of_optiont
      (fun x ->
         let uu____235 =
           let uu____236 = FStar_Parser_AST.string_of_fsdoc x in
           Prims.strcat uu____236 "*)" in
         Prims.strcat "(*" uu____235) "" d
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t -> string_of_optiont FStar_Parser_AST.term_to_string "" t
let (code_wrap : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____256 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____267 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1, _bb, _ko, fields) ->
        let uu____312 =
          let uu____313 =
            let uu____314 =
              let uu____315 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____364 ->
                        match uu____364 with
                        | (id2, t, doco) ->
                            let uu____410 = string_of_fsdoco doco in
                            let uu____411 =
                              let uu____412 =
                                let uu____413 =
                                  FStar_Parser_AST.term_to_string t in
                                Prims.strcat ":" uu____413 in
                              Prims.strcat id2.FStar_Ident.idText uu____412 in
                            Prims.strcat uu____410 uu____411)) in
              FStar_All.pipe_right uu____315 (FStar_String.concat "; ") in
            Prims.strcat uu____314 " }" in
          Prims.strcat " = { " uu____313 in
        Prims.strcat id1.FStar_Ident.idText uu____312
    | FStar_Parser_AST.TyconVariant (id1, _bb, _ko, vars) ->
        let uu____456 =
          let uu____457 =
            let uu____458 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____516 ->
                      match uu____516 with
                      | (id2, trmo, doco, u) ->
                          let uu____571 = string_of_fsdoco doco in
                          let uu____572 =
                            let uu____573 =
                              let uu____574 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo in
                              Prims.strcat ":" uu____574 in
                            Prims.strcat id2.FStar_Ident.idText uu____573 in
                          Prims.strcat uu____571 uu____572)) in
            FStar_All.pipe_right uu____458 (FStar_String.concat " | ") in
          Prims.strcat " = " uu____457 in
        Prims.strcat id1.FStar_Ident.idText uu____456
let (string_of_decl' : FStar_Parser_AST.decl' -> Prims.string) =
  fun d ->
    match d with
    | FStar_Parser_AST.TopLevelModule l ->
        Prims.strcat "module " l.FStar_Ident.str
    | FStar_Parser_AST.Open l -> Prims.strcat "open " l.FStar_Ident.str
    | FStar_Parser_AST.Include l -> Prims.strcat "include " l.FStar_Ident.str
    | FStar_Parser_AST.Friend l -> Prims.strcat "friend " l.FStar_Ident.str
    | FStar_Parser_AST.ModuleAbbrev (i, l) ->
        Prims.strcat "module "
          (Prims.strcat i.FStar_Ident.idText
             (Prims.strcat " = " l.FStar_Ident.str))
    | FStar_Parser_AST.TopLevelLet (uu____588, pats) ->
        let termty =
          FStar_List.map
            (fun uu____622 ->
               match uu____622 with
               | (p, t) ->
                   let uu____633 = FStar_Parser_AST.pat_to_string p in
                   let uu____634 = FStar_Parser_AST.term_to_string t in
                   (uu____633, uu____634)) pats in
        let termty' =
          FStar_List.map
            (fun uu____645 ->
               match uu____645 with
               | (p, t) -> Prims.strcat p (Prims.strcat ":" t)) termty in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____652 -> "main ..."
    | FStar_Parser_AST.Assume (i, t) ->
        let uu____655 =
          let uu____656 =
            let uu____657 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____657 in
          Prims.strcat i.FStar_Ident.idText uu____656 in
        Prims.strcat "assume " uu____655
    | FStar_Parser_AST.Tycon (uu____658, tc, tys) ->
        let s = if tc then "class" else "type" in
        let uu____679 =
          let uu____680 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____724 ->
                    match uu____724 with
                    | (t, d1) ->
                        let uu____767 = string_of_tycon t in
                        let uu____768 =
                          let uu____769 = string_of_fsdoco d1 in
                          Prims.strcat " " uu____769 in
                        Prims.strcat uu____767 uu____768)) in
          FStar_All.pipe_right uu____680 (FStar_String.concat " and ") in
        Prims.strcat s uu____679
    | FStar_Parser_AST.Val (i, t) ->
        let uu____774 =
          let uu____775 =
            let uu____776 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____776 in
          Prims.strcat i.FStar_Ident.idText uu____775 in
        Prims.strcat "val " uu____774
    | FStar_Parser_AST.Exception (i, uu____778) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i, uu____784, uu____785, uu____786)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i, uu____796, uu____797)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____802 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____803 -> "pragma"
    | FStar_Parser_AST.Splice (ids, t) ->
        let uu____810 = FStar_Parser_AST.term_to_string t in
        Prims.strcat "splice " uu____810
    | FStar_Parser_AST.Fsdoc (comm, uu____812) -> comm
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____858 -> false
        | FStar_Parser_AST.TyconAbbrev uu____869 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____882, uu____883, uu____884, fields) ->
            FStar_List.existsb
              (fun uu____926 ->
                 match uu____926 with
                 | (_id, _t, doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____942, uu____943, uu____944, vars) ->
            FStar_List.existsb
              (fun uu____999 ->
                 match uu____999 with
                 | (_id, _t, doco, _u) -> FStar_Util.is_some doco) vars in
      FStar_List.existsb
        (fun uu____1033 ->
           match uu____1033 with
           | (tycon, doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____1046 -> true
    | uu____1047 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____1050 -> true
         | FStar_Parser_AST.Tycon (uu____1051, uu____1052, ty) ->
             tycon_documented ty
         | uu____1070 -> false)
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w ->
    fun d ->
      if decl_documented d
      then
        let uu____1086 = d in
        match uu____1086 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1088;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1090;
            FStar_Parser_AST.attrs = uu____1091;_} ->
            ((let uu____1095 =
                let uu____1096 = string_of_decl' d.FStar_Parser_AST.d in
                code_wrap uu____1096 in
              w uu____1095);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1, _kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1112 -> ());
             w "")
      else ()
let document_toplevel :
  'Auu____1122 .
    'Auu____1122 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,
          Prims.string FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun name ->
    fun topdecl ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1141 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1, kw) ->
               let uu____1164 =
                 FStar_List.tryFind
                   (fun uu____1178 ->
                      match uu____1178 with | (k, v1) -> k = "summary") kw in
               (match uu____1164 with
                | FStar_Pervasives_Native.None ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1201, summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1215 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m ->
    let uu____1229 =
      match m with
      | FStar_Parser_AST.Module (n1, d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1, d, uu____1256) ->
          (n1, d, "interface") in
    match uu____1229 with
    | (name, decls, _mt) ->
        let uu____1270 = one_toplevel decls in
        (match uu____1270 with
         | FStar_Pervasives_Native.Some (top_decl, other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md") in
             let fd = FStar_Util.open_file_for_writing on in
             let w = FStar_Util.append_to_file fd in
             let no_summary = "fsdoc: no-summary-found" in
             let no_comment = "fsdoc: no-comment-found" in
             let uu____1300 = document_toplevel name top_decl in
             (match uu____1300 with
              | (summary, comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None -> no_summary in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None -> no_comment in
                  ((let uu____1324 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str] in
                    w uu____1324);
                   (let uu____1326 = FStar_Util.format "%s\n" [summary1] in
                    w uu____1326);
                   (let uu____1328 = FStar_Util.format "%s\n" [comment1] in
                    w uu____1328);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None ->
             let uu____1337 =
               let uu____1342 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____1342) in
             FStar_Errors.raise_err uu____1337)
let (generate : Prims.string Prims.list -> unit) =
  fun files ->
    let modules =
      FStar_List.map
        (fun fn ->
           let uu____1358 = FStar_Parser_Driver.parse_file fn in
           FStar_Pervasives_Native.fst uu____1358) files in
    let mods = FStar_List.map document_module modules in
    let on = FStar_Options.prepend_output_dir "index.md" in
    let fd = FStar_Util.open_file_for_writing on in
    FStar_List.iter
      (fun m ->
         let uu____1384 = FStar_Util.format "%s\n" [m.FStar_Ident.str] in
         FStar_Util.append_to_file fd uu____1384) mods;
    FStar_Util.close_file fd