open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____18 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____30 -> true
           | uu____31 -> false) decls
       in
    match uu____18 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____67 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 
  | Branch of mforest FStar_Util.smap [@@deriving show]
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____100 -> false
  
let (__proj__Leaf__item___0 :
  mforest -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____128 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____154 'Auu____155 .
    ('Auu____154 -> 'Auu____155) ->
      'Auu____155 ->
        'Auu____154 FStar_Pervasives_Native.option -> 'Auu____155
  =
  fun f  ->
    fun y  ->
      fun xo  ->
        match xo with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> y
  
let (string_of_fsdoco :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
    Prims.string)
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____233 =
           let uu____234 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat uu____234 "*)"  in
         Prims.strcat "(*" uu____233) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____254 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____265 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____310 =
          let uu____311 =
            let uu____312 =
              let uu____313 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____352  ->
                        match uu____352 with
                        | (id2,t,doco) ->
                            let uu____398 = string_of_fsdoco doco  in
                            let uu____399 =
                              let uu____400 =
                                let uu____401 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" uu____401  in
                              Prims.strcat id2.FStar_Ident.idText uu____400
                               in
                            Prims.strcat uu____398 uu____399))
                 in
              FStar_All.pipe_right uu____313 (FStar_String.concat "; ")  in
            Prims.strcat uu____312 " }"  in
          Prims.strcat " = { " uu____311  in
        Prims.strcat id1.FStar_Ident.idText uu____310
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____444 =
          let uu____445 =
            let uu____446 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____494  ->
                      match uu____494 with
                      | (id2,trmo,doco,u) ->
                          let uu____549 = string_of_fsdoco doco  in
                          let uu____550 =
                            let uu____551 =
                              let uu____552 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" uu____552  in
                            Prims.strcat id2.FStar_Ident.idText uu____551  in
                          Prims.strcat uu____549 uu____550))
               in
            FStar_All.pipe_right uu____446 (FStar_String.concat " | ")  in
          Prims.strcat " = " uu____445  in
        Prims.strcat id1.FStar_Ident.idText uu____444
  
let (string_of_decl' : FStar_Parser_AST.decl' -> Prims.string) =
  fun d  ->
    match d with
    | FStar_Parser_AST.TopLevelModule l ->
        Prims.strcat "module " l.FStar_Ident.str
    | FStar_Parser_AST.Open l -> Prims.strcat "open " l.FStar_Ident.str
    | FStar_Parser_AST.Include l -> Prims.strcat "include " l.FStar_Ident.str
    | FStar_Parser_AST.ModuleAbbrev (i,l) ->
        Prims.strcat "module "
          (Prims.strcat i.FStar_Ident.idText
             (Prims.strcat " = " l.FStar_Ident.str))
    | FStar_Parser_AST.TopLevelLet (uu____565,pats) ->
        let termty =
          FStar_List.map
            (fun uu____599  ->
               match uu____599 with
               | (p,t) ->
                   let uu____610 = FStar_Parser_AST.pat_to_string p  in
                   let uu____611 = FStar_Parser_AST.term_to_string t  in
                   (uu____610, uu____611)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____622  ->
               match uu____622 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____629 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____632 =
          let uu____633 =
            let uu____634 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____634  in
          Prims.strcat i.FStar_Ident.idText uu____633  in
        Prims.strcat "assume " uu____632
    | FStar_Parser_AST.Tycon (uu____635,tys) ->
        let uu____653 =
          let uu____654 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____688  ->
                    match uu____688 with
                    | (t,d1) ->
                        let uu____731 = string_of_tycon t  in
                        let uu____732 =
                          let uu____733 = string_of_fsdoco d1  in
                          Prims.strcat " " uu____733  in
                        Prims.strcat uu____731 uu____732))
             in
          FStar_All.pipe_right uu____654 (FStar_String.concat " and ")  in
        Prims.strcat "type " uu____653
    | FStar_Parser_AST.Val (i,t) ->
        let uu____738 =
          let uu____739 =
            let uu____740 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____740  in
          Prims.strcat i.FStar_Ident.idText uu____739  in
        Prims.strcat "val " uu____738
    | FStar_Parser_AST.Exception (i,uu____742) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____748,uu____749,uu____750)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____760,uu____761)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____766 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____767 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____774 = FStar_Parser_AST.term_to_string t  in
        Prims.strcat "splice " uu____774
    | FStar_Parser_AST.Fsdoc (comm,uu____776) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____820 -> false
        | FStar_Parser_AST.TyconAbbrev uu____831 -> false
        | FStar_Parser_AST.TyconRecord (uu____844,uu____845,uu____846,fields)
            ->
            FStar_List.existsb
              (fun uu____888  ->
                 match uu____888 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____904,uu____905,uu____906,vars)
            ->
            FStar_List.existsb
              (fun uu____961  ->
                 match uu____961 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____995  ->
           match uu____995 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____1008 -> true
    | uu____1009 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____1012 -> true
         | FStar_Parser_AST.Tycon (uu____1013,ty) -> tycon_documented ty
         | uu____1031 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1047 = d  in
        match uu____1047 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1049;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1051;
            FStar_Parser_AST.attrs = uu____1052;_} ->
            let uu____1055 =
              let uu____1056 =
                let uu____1057 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____1057  in
              w uu____1056  in
            let uu____1058 =
              match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1083 -> ()  in
            w ""
      else ()
  
let document_toplevel :
  'Auu____1093 .
    'Auu____1093 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1112 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____1145 =
                 FStar_List.tryFind
                   (fun uu____1159  ->
                      match uu____1159 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____1145 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1182,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1196 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lid) =
  fun m  ->
    let uu____1210 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1237) -> (n1, d, "interface")
       in
    match uu____1210 with
    | (name,decls,_mt) ->
        let uu____1251 = one_toplevel decls  in
        (match uu____1251 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____1280 = document_toplevel name top_decl  in
             (match uu____1280 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  let uu____1303 =
                    let uu____1304 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____1304  in
                  let uu____1305 =
                    let uu____1306 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____1306  in
                  let uu____1307 =
                    let uu____1308 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____1308  in
                  let uu____1309 =
                    FStar_List.iter (document_decl w) other_decls  in
                  let uu____1310 = FStar_Util.close_file fd  in name)
         | FStar_Pervasives_Native.None  ->
             let uu____1317 =
               let uu____1322 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____1322)  in
             FStar_Errors.raise_err uu____1317)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____1338 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____1338) files
       in
    let mods = FStar_List.map document_module modules  in
    let on = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on  in
    let uu____1360 =
      FStar_List.iter
        (fun m  ->
           let uu____1364 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
           FStar_Util.append_to_file fd uu____1364) mods
       in
    FStar_Util.close_file fd
  