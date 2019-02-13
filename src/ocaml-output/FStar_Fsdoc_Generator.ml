open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native_Tuple2.tuple2 FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____18 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____31 -> true
           | uu____33 -> false) decls
       in
    match uu____18 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____70 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string,Prims.string) FStar_Pervasives_Native_Tuple2.tuple2
  
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____113 -> false
  
let (__proj__Leaf__item___0 :
  mforest ->
    (Prims.string,Prims.string) FStar_Pervasives_Native_Tuple2.tuple2)
  = fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____153 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____184 'Auu____185 .
    ('Auu____184 -> 'Auu____185) ->
      'Auu____185 ->
        'Auu____184 FStar_Pervasives_Native.option -> 'Auu____185
  =
  fun f  ->
    fun y  ->
      fun xo  ->
        match xo with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> y
  
let (string_of_fsdoco :
  (Prims.string,(Prims.string,Prims.string)
                  FStar_Pervasives_Native_Tuple2.tuple2 Prims.list)
    FStar_Pervasives_Native_Tuple2.tuple2 FStar_Pervasives_Native.option ->
    Prims.string)
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____278 =
           let uu____280 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat uu____280 "*)"  in
         Prims.strcat "(*" uu____278) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____317 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____329 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____375 =
          let uu____377 =
            let uu____379 =
              let uu____381 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____439  ->
                        match uu____439 with
                        | (id2,t,doco) ->
                            let uu____495 = string_of_fsdoco doco  in
                            let uu____497 =
                              let uu____499 =
                                let uu____501 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" uu____501  in
                              Prims.strcat id2.FStar_Ident.idText uu____499
                               in
                            Prims.strcat uu____495 uu____497))
                 in
              FStar_All.pipe_right uu____381 (FStar_String.concat "; ")  in
            Prims.strcat uu____379 " }"  in
          Prims.strcat " = { " uu____377  in
        Prims.strcat id1.FStar_Ident.idText uu____375
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____553 =
          let uu____555 =
            let uu____557 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____626  ->
                      match uu____626 with
                      | (id2,trmo,doco,u) ->
                          let uu____694 = string_of_fsdoco doco  in
                          let uu____696 =
                            let uu____698 =
                              let uu____700 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" uu____700  in
                            Prims.strcat id2.FStar_Ident.idText uu____698  in
                          Prims.strcat uu____694 uu____696))
               in
            FStar_All.pipe_right uu____557 (FStar_String.concat " | ")  in
          Prims.strcat " = " uu____555  in
        Prims.strcat id1.FStar_Ident.idText uu____553
  
let (string_of_decl' : FStar_Parser_AST.decl' -> Prims.string) =
  fun d  ->
    match d with
    | FStar_Parser_AST.TopLevelModule l ->
        Prims.strcat "module " l.FStar_Ident.str
    | FStar_Parser_AST.Open l -> Prims.strcat "open " l.FStar_Ident.str
    | FStar_Parser_AST.Include l -> Prims.strcat "include " l.FStar_Ident.str
    | FStar_Parser_AST.Friend l -> Prims.strcat "friend " l.FStar_Ident.str
    | FStar_Parser_AST.ModuleAbbrev (i,l) ->
        Prims.strcat "module "
          (Prims.strcat i.FStar_Ident.idText
             (Prims.strcat " = " l.FStar_Ident.str))
    | FStar_Parser_AST.TopLevelLet (uu____731,pats) ->
        let termty =
          FStar_List.map
            (fun uu____769  ->
               match uu____769 with
               | (p,t) ->
                   let uu____782 = FStar_Parser_AST.pat_to_string p  in
                   let uu____784 = FStar_Parser_AST.term_to_string t  in
                   (uu____782, uu____784)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____802  ->
               match uu____802 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____819 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____823 =
          let uu____825 =
            let uu____827 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____827  in
          Prims.strcat i.FStar_Ident.idText uu____825  in
        Prims.strcat "assume " uu____823
    | FStar_Parser_AST.Tycon (uu____831,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____862 =
          let uu____864 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____917  ->
                    match uu____917 with
                    | (t,d1) ->
                        let uu____970 = string_of_tycon t  in
                        let uu____972 =
                          let uu____974 = string_of_fsdoco d1  in
                          Prims.strcat " " uu____974  in
                        Prims.strcat uu____970 uu____972))
             in
          FStar_All.pipe_right uu____864 (FStar_String.concat " and ")  in
        Prims.strcat s uu____862
    | FStar_Parser_AST.Val (i,t) ->
        let uu____984 =
          let uu____986 =
            let uu____988 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____988  in
          Prims.strcat i.FStar_Ident.idText uu____986  in
        Prims.strcat "val " uu____984
    | FStar_Parser_AST.Exception (i,uu____993) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____1000,uu____1001,uu____1002)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____1013,uu____1014)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____1020 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____1022 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____1030 = FStar_Parser_AST.term_to_string t  in
        Prims.strcat "splice " uu____1030
    | FStar_Parser_AST.Fsdoc (comm,uu____1034) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____1091 -> false
        | FStar_Parser_AST.TyconAbbrev uu____1103 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____1117,uu____1118,uu____1119,fields) ->
            FStar_List.existsb
              (fun uu____1161  ->
                 match uu____1161 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____1178,uu____1179,uu____1180,vars) ->
            FStar_List.existsb
              (fun uu____1238  ->
                 match uu____1238 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____1276  ->
           match uu____1276 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____1291 -> true
    | uu____1293 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____1297 -> true
         | FStar_Parser_AST.Tycon (uu____1299,uu____1300,ty) ->
             tycon_documented ty
         | uu____1322 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1343 = d  in
        match uu____1343 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1345;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1347;
            FStar_Parser_AST.attrs = uu____1348;_} ->
            ((let uu____1352 =
                let uu____1354 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____1354  in
              w uu____1352);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1378 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____1391 .
    'Auu____1391 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native_Tuple2.tuple2
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1412 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____1443 =
                 FStar_List.tryFind
                   (fun uu____1461  ->
                      match uu____1461 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____1443 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1501,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1529 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____1548 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1579) -> (n1, d, "interface")
       in
    match uu____1548 with
    | (name,decls,_mt) ->
        let uu____1599 = one_toplevel decls  in
        (match uu____1599 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____1636 = document_toplevel name top_decl  in
             (match uu____1636 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____1676 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____1676);
                   (let uu____1682 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____1682);
                   (let uu____1688 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____1688);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____1701 =
               let uu____1707 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____1707)  in
             FStar_Errors.raise_err uu____1701)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____1731 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____1731) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____1761 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____1761) mods;
    FStar_Util.close_file fd
  