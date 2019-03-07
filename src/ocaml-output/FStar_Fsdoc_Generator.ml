open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____48976 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____48989 -> true
           | uu____48991 -> false) decls
       in
    match uu____48976 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____49028 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____49071 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____49110 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____49140 'Auu____49141 .
    ('Auu____49140 -> 'Auu____49141) ->
      'Auu____49141 ->
        'Auu____49140 FStar_Pervasives_Native.option -> 'Auu____49141
  =
  fun f  ->
    fun y  ->
      fun xo  ->
        match xo with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> y
  
let (string_of_fsdoco :
  (Prims.string * (Prims.string * Prims.string) Prims.list)
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____49234 =
           let uu____49236 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____49236 "*)"  in
         Prims.op_Hat "(*" uu____49234) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____49273 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____49285 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____49331 =
          let uu____49333 =
            let uu____49335 =
              let uu____49337 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____49395  ->
                        match uu____49395 with
                        | (id2,t,doco) ->
                            let uu____49451 = string_of_fsdoco doco  in
                            let uu____49453 =
                              let uu____49455 =
                                let uu____49457 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____49457  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____49455
                               in
                            Prims.op_Hat uu____49451 uu____49453))
                 in
              FStar_All.pipe_right uu____49337 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____49335 " }"  in
          Prims.op_Hat " = { " uu____49333  in
        Prims.op_Hat id1.FStar_Ident.idText uu____49331
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____49509 =
          let uu____49511 =
            let uu____49513 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____49582  ->
                      match uu____49582 with
                      | (id2,trmo,doco,u) ->
                          let uu____49650 = string_of_fsdoco doco  in
                          let uu____49652 =
                            let uu____49654 =
                              let uu____49656 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____49656  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____49654
                             in
                          Prims.op_Hat uu____49650 uu____49652))
               in
            FStar_All.pipe_right uu____49513 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____49511  in
        Prims.op_Hat id1.FStar_Ident.idText uu____49509
  
let (string_of_decl' : FStar_Parser_AST.decl' -> Prims.string) =
  fun d  ->
    match d with
    | FStar_Parser_AST.TopLevelModule l ->
        Prims.op_Hat "module " l.FStar_Ident.str
    | FStar_Parser_AST.Open l -> Prims.op_Hat "open " l.FStar_Ident.str
    | FStar_Parser_AST.Include l -> Prims.op_Hat "include " l.FStar_Ident.str
    | FStar_Parser_AST.Friend l -> Prims.op_Hat "friend " l.FStar_Ident.str
    | FStar_Parser_AST.ModuleAbbrev (i,l) ->
        Prims.op_Hat "module "
          (Prims.op_Hat i.FStar_Ident.idText
             (Prims.op_Hat " = " l.FStar_Ident.str))
    | FStar_Parser_AST.TopLevelLet (uu____49687,pats) ->
        let termty =
          FStar_List.map
            (fun uu____49725  ->
               match uu____49725 with
               | (p,t) ->
                   let uu____49738 = FStar_Parser_AST.pat_to_string p  in
                   let uu____49740 = FStar_Parser_AST.term_to_string t  in
                   (uu____49738, uu____49740)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____49758  ->
               match uu____49758 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____49775 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____49779 =
          let uu____49781 =
            let uu____49783 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____49783  in
          Prims.op_Hat i.FStar_Ident.idText uu____49781  in
        Prims.op_Hat "assume " uu____49779
    | FStar_Parser_AST.Tycon (uu____49787,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____49818 =
          let uu____49820 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____49873  ->
                    match uu____49873 with
                    | (t,d1) ->
                        let uu____49926 = string_of_tycon t  in
                        let uu____49928 =
                          let uu____49930 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____49930  in
                        Prims.op_Hat uu____49926 uu____49928))
             in
          FStar_All.pipe_right uu____49820 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____49818
    | FStar_Parser_AST.Val (i,t) ->
        let uu____49940 =
          let uu____49942 =
            let uu____49944 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____49944  in
          Prims.op_Hat i.FStar_Ident.idText uu____49942  in
        Prims.op_Hat "val " uu____49940
    | FStar_Parser_AST.Exception (i,uu____49949) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____49956,uu____49957,uu____49958)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____49969,uu____49970)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____49976 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____49978 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____49986 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____49986
    | FStar_Parser_AST.Fsdoc (comm,uu____49990) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____50047 -> false
        | FStar_Parser_AST.TyconAbbrev uu____50059 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____50073,uu____50074,uu____50075,fields) ->
            FStar_List.existsb
              (fun uu____50117  ->
                 match uu____50117 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____50134,uu____50135,uu____50136,vars) ->
            FStar_List.existsb
              (fun uu____50194  ->
                 match uu____50194 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____50232  ->
           match uu____50232 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____50247 -> true
    | uu____50249 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____50253 -> true
         | FStar_Parser_AST.Tycon (uu____50255,uu____50256,ty) ->
             tycon_documented ty
         | uu____50278 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____50299 = d  in
        match uu____50299 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____50301;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____50303;
            FStar_Parser_AST.attrs = uu____50304;_} ->
            ((let uu____50308 =
                let uu____50310 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____50310  in
              w uu____50308);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____50334 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____50347 .
    'Auu____50347 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____50368 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____50399 =
                 FStar_List.tryFind
                   (fun uu____50417  ->
                      match uu____50417 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____50399 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____50457,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____50485 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____50504 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____50535) -> (n1, d, "interface")
       in
    match uu____50504 with
    | (name,decls,_mt) ->
        let uu____50555 = one_toplevel decls  in
        (match uu____50555 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____50592 = document_toplevel name top_decl  in
             (match uu____50592 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____50632 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____50632);
                   (let uu____50638 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____50638);
                   (let uu____50644 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____50644);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____50657 =
               let uu____50663 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____50663)  in
             FStar_Errors.raise_err uu____50657)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____50687 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____50687) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____50717 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____50717) mods;
    FStar_Util.close_file fd
  