open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____53616 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____53629 -> true
           | uu____53631 -> false) decls
       in
    match uu____53616 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____53668 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____53711 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____53751 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____53782 'Auu____53783 .
    ('Auu____53782 -> 'Auu____53783) ->
      'Auu____53783 ->
        'Auu____53782 FStar_Pervasives_Native.option -> 'Auu____53783
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
         let uu____53876 =
           let uu____53878 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____53878 "*)"  in
         Prims.op_Hat "(*" uu____53876) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____53915 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____53927 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____53973 =
          let uu____53975 =
            let uu____53977 =
              let uu____53979 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____54037  ->
                        match uu____54037 with
                        | (id2,t,doco) ->
                            let uu____54093 = string_of_fsdoco doco  in
                            let uu____54095 =
                              let uu____54097 =
                                let uu____54099 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____54099  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____54097
                               in
                            Prims.op_Hat uu____54093 uu____54095))
                 in
              FStar_All.pipe_right uu____53979 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____53977 " }"  in
          Prims.op_Hat " = { " uu____53975  in
        Prims.op_Hat id1.FStar_Ident.idText uu____53973
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____54151 =
          let uu____54153 =
            let uu____54155 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____54224  ->
                      match uu____54224 with
                      | (id2,trmo,doco,u) ->
                          let uu____54292 = string_of_fsdoco doco  in
                          let uu____54294 =
                            let uu____54296 =
                              let uu____54298 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____54298  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____54296
                             in
                          Prims.op_Hat uu____54292 uu____54294))
               in
            FStar_All.pipe_right uu____54155 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____54153  in
        Prims.op_Hat id1.FStar_Ident.idText uu____54151
  
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
    | FStar_Parser_AST.TopLevelLet (uu____54329,pats) ->
        let termty =
          FStar_List.map
            (fun uu____54367  ->
               match uu____54367 with
               | (p,t) ->
                   let uu____54380 = FStar_Parser_AST.pat_to_string p  in
                   let uu____54382 = FStar_Parser_AST.term_to_string t  in
                   (uu____54380, uu____54382)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____54400  ->
               match uu____54400 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____54417 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____54421 =
          let uu____54423 =
            let uu____54425 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54425  in
          Prims.op_Hat i.FStar_Ident.idText uu____54423  in
        Prims.op_Hat "assume " uu____54421
    | FStar_Parser_AST.Tycon (uu____54429,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____54460 =
          let uu____54462 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____54515  ->
                    match uu____54515 with
                    | (t,d1) ->
                        let uu____54568 = string_of_tycon t  in
                        let uu____54570 =
                          let uu____54572 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____54572  in
                        Prims.op_Hat uu____54568 uu____54570))
             in
          FStar_All.pipe_right uu____54462 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____54460
    | FStar_Parser_AST.Val (i,t) ->
        let uu____54582 =
          let uu____54584 =
            let uu____54586 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54586  in
          Prims.op_Hat i.FStar_Ident.idText uu____54584  in
        Prims.op_Hat "val " uu____54582
    | FStar_Parser_AST.Exception (i,uu____54591) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____54598,uu____54599,uu____54600)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____54611,uu____54612)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____54618 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____54620 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____54628 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____54628
    | FStar_Parser_AST.Fsdoc (comm,uu____54632) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____54689 -> false
        | FStar_Parser_AST.TyconAbbrev uu____54701 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____54715,uu____54716,uu____54717,fields) ->
            FStar_List.existsb
              (fun uu____54759  ->
                 match uu____54759 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____54776,uu____54777,uu____54778,vars) ->
            FStar_List.existsb
              (fun uu____54836  ->
                 match uu____54836 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____54874  ->
           match uu____54874 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____54889 -> true
    | uu____54891 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54895 -> true
         | FStar_Parser_AST.Tycon (uu____54897,uu____54898,ty) ->
             tycon_documented ty
         | uu____54920 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____54941 = d  in
        match uu____54941 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____54943;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____54945;
            FStar_Parser_AST.attrs = uu____54946;_} ->
            ((let uu____54950 =
                let uu____54952 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____54952  in
              w uu____54950);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____54976 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____54989 .
    'Auu____54989 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____55010 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____55041 =
                 FStar_List.tryFind
                   (fun uu____55059  ->
                      match uu____55059 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____55041 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____55099,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____55127 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____55146 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____55177) -> (n1, d, "interface")
       in
    match uu____55146 with
    | (name,decls,_mt) ->
        let uu____55197 = one_toplevel decls  in
        (match uu____55197 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____55234 = document_toplevel name top_decl  in
             (match uu____55234 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____55274 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____55274);
                   (let uu____55280 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____55280);
                   (let uu____55286 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____55286);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____55299 =
               let uu____55305 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____55305)  in
             FStar_Errors.raise_err uu____55299)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____55329 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____55329) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____55359 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____55359) mods;
    FStar_Util.close_file fd
  