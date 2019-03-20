open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____48989 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____49002 -> true
           | uu____49004 -> false) decls
       in
    match uu____48989 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____49041 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____49084 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____49123 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____49153 'Auu____49154 .
    ('Auu____49153 -> 'Auu____49154) ->
      'Auu____49154 ->
        'Auu____49153 FStar_Pervasives_Native.option -> 'Auu____49154
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
         let uu____49247 =
           let uu____49249 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____49249 "*)"  in
         Prims.op_Hat "(*" uu____49247) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____49286 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____49298 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____49344 =
          let uu____49346 =
            let uu____49348 =
              let uu____49350 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____49408  ->
                        match uu____49408 with
                        | (id2,t,doco) ->
                            let uu____49464 = string_of_fsdoco doco  in
                            let uu____49466 =
                              let uu____49468 =
                                let uu____49470 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____49470  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____49468
                               in
                            Prims.op_Hat uu____49464 uu____49466))
                 in
              FStar_All.pipe_right uu____49350 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____49348 " }"  in
          Prims.op_Hat " = { " uu____49346  in
        Prims.op_Hat id1.FStar_Ident.idText uu____49344
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____49522 =
          let uu____49524 =
            let uu____49526 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____49595  ->
                      match uu____49595 with
                      | (id2,trmo,doco,u) ->
                          let uu____49663 = string_of_fsdoco doco  in
                          let uu____49665 =
                            let uu____49667 =
                              let uu____49669 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____49669  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____49667
                             in
                          Prims.op_Hat uu____49663 uu____49665))
               in
            FStar_All.pipe_right uu____49526 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____49524  in
        Prims.op_Hat id1.FStar_Ident.idText uu____49522
  
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
    | FStar_Parser_AST.TopLevelLet (uu____49700,pats) ->
        let termty =
          FStar_List.map
            (fun uu____49738  ->
               match uu____49738 with
               | (p,t) ->
                   let uu____49751 = FStar_Parser_AST.pat_to_string p  in
                   let uu____49753 = FStar_Parser_AST.term_to_string t  in
                   (uu____49751, uu____49753)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____49771  ->
               match uu____49771 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____49788 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____49792 =
          let uu____49794 =
            let uu____49796 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____49796  in
          Prims.op_Hat i.FStar_Ident.idText uu____49794  in
        Prims.op_Hat "assume " uu____49792
    | FStar_Parser_AST.Tycon (uu____49800,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____49831 =
          let uu____49833 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____49886  ->
                    match uu____49886 with
                    | (t,d1) ->
                        let uu____49939 = string_of_tycon t  in
                        let uu____49941 =
                          let uu____49943 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____49943  in
                        Prims.op_Hat uu____49939 uu____49941))
             in
          FStar_All.pipe_right uu____49833 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____49831
    | FStar_Parser_AST.Val (i,t) ->
        let uu____49953 =
          let uu____49955 =
            let uu____49957 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____49957  in
          Prims.op_Hat i.FStar_Ident.idText uu____49955  in
        Prims.op_Hat "val " uu____49953
    | FStar_Parser_AST.Exception (i,uu____49962) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____49969,uu____49970,uu____49971)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____49982,uu____49983)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____49989 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____49991 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____49999 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____49999
    | FStar_Parser_AST.Fsdoc (comm,uu____50003) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____50060 -> false
        | FStar_Parser_AST.TyconAbbrev uu____50072 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____50086,uu____50087,uu____50088,fields) ->
            FStar_List.existsb
              (fun uu____50130  ->
                 match uu____50130 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____50147,uu____50148,uu____50149,vars) ->
            FStar_List.existsb
              (fun uu____50207  ->
                 match uu____50207 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____50245  ->
           match uu____50245 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____50260 -> true
    | uu____50262 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____50266 -> true
         | FStar_Parser_AST.Tycon (uu____50268,uu____50269,ty) ->
             tycon_documented ty
         | uu____50291 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____50312 = d  in
        match uu____50312 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____50314;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____50316;
            FStar_Parser_AST.attrs = uu____50317;_} ->
            ((let uu____50321 =
                let uu____50323 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____50323  in
              w uu____50321);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____50347 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____50360 .
    'Auu____50360 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____50381 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____50412 =
                 FStar_List.tryFind
                   (fun uu____50430  ->
                      match uu____50430 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____50412 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____50470,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____50498 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____50517 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____50548) -> (n1, d, "interface")
       in
    match uu____50517 with
    | (name,decls,_mt) ->
        let uu____50568 = one_toplevel decls  in
        (match uu____50568 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____50605 = document_toplevel name top_decl  in
             (match uu____50605 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____50645 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____50645);
                   (let uu____50651 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____50651);
                   (let uu____50657 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____50657);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____50670 =
               let uu____50676 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____50676)  in
             FStar_Errors.raise_err uu____50670)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____50700 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____50700) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____50730 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____50730) mods;
    FStar_Util.close_file fd
  