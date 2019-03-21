open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____49009 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____49022 -> true
           | uu____49024 -> false) decls
       in
    match uu____49009 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____49061 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____49104 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____49143 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____49173 'Auu____49174 .
    ('Auu____49173 -> 'Auu____49174) ->
      'Auu____49174 ->
        'Auu____49173 FStar_Pervasives_Native.option -> 'Auu____49174
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
         let uu____49267 =
           let uu____49269 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____49269 "*)"  in
         Prims.op_Hat "(*" uu____49267) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____49306 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____49318 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____49364 =
          let uu____49366 =
            let uu____49368 =
              let uu____49370 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____49428  ->
                        match uu____49428 with
                        | (id2,t,doco) ->
                            let uu____49484 = string_of_fsdoco doco  in
                            let uu____49486 =
                              let uu____49488 =
                                let uu____49490 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____49490  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____49488
                               in
                            Prims.op_Hat uu____49484 uu____49486))
                 in
              FStar_All.pipe_right uu____49370 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____49368 " }"  in
          Prims.op_Hat " = { " uu____49366  in
        Prims.op_Hat id1.FStar_Ident.idText uu____49364
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____49542 =
          let uu____49544 =
            let uu____49546 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____49615  ->
                      match uu____49615 with
                      | (id2,trmo,doco,u) ->
                          let uu____49683 = string_of_fsdoco doco  in
                          let uu____49685 =
                            let uu____49687 =
                              let uu____49689 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____49689  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____49687
                             in
                          Prims.op_Hat uu____49683 uu____49685))
               in
            FStar_All.pipe_right uu____49546 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____49544  in
        Prims.op_Hat id1.FStar_Ident.idText uu____49542
  
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
    | FStar_Parser_AST.TopLevelLet (uu____49720,pats) ->
        let termty =
          FStar_List.map
            (fun uu____49758  ->
               match uu____49758 with
               | (p,t) ->
                   let uu____49771 = FStar_Parser_AST.pat_to_string p  in
                   let uu____49773 = FStar_Parser_AST.term_to_string t  in
                   (uu____49771, uu____49773)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____49791  ->
               match uu____49791 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____49808 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____49812 =
          let uu____49814 =
            let uu____49816 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____49816  in
          Prims.op_Hat i.FStar_Ident.idText uu____49814  in
        Prims.op_Hat "assume " uu____49812
    | FStar_Parser_AST.Tycon (uu____49820,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____49851 =
          let uu____49853 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____49906  ->
                    match uu____49906 with
                    | (t,d1) ->
                        let uu____49959 = string_of_tycon t  in
                        let uu____49961 =
                          let uu____49963 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____49963  in
                        Prims.op_Hat uu____49959 uu____49961))
             in
          FStar_All.pipe_right uu____49853 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____49851
    | FStar_Parser_AST.Val (i,t) ->
        let uu____49973 =
          let uu____49975 =
            let uu____49977 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____49977  in
          Prims.op_Hat i.FStar_Ident.idText uu____49975  in
        Prims.op_Hat "val " uu____49973
    | FStar_Parser_AST.Exception (i,uu____49982) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____49989,uu____49990,uu____49991)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____50002,uu____50003)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____50009 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____50011 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____50019 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____50019
    | FStar_Parser_AST.Fsdoc (comm,uu____50023) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____50080 -> false
        | FStar_Parser_AST.TyconAbbrev uu____50092 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____50106,uu____50107,uu____50108,fields) ->
            FStar_List.existsb
              (fun uu____50150  ->
                 match uu____50150 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____50167,uu____50168,uu____50169,vars) ->
            FStar_List.existsb
              (fun uu____50227  ->
                 match uu____50227 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____50265  ->
           match uu____50265 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____50280 -> true
    | uu____50282 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____50286 -> true
         | FStar_Parser_AST.Tycon (uu____50288,uu____50289,ty) ->
             tycon_documented ty
         | uu____50311 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____50332 = d  in
        match uu____50332 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____50334;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____50336;
            FStar_Parser_AST.attrs = uu____50337;_} ->
            ((let uu____50341 =
                let uu____50343 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____50343  in
              w uu____50341);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____50367 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____50380 .
    'Auu____50380 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____50401 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____50432 =
                 FStar_List.tryFind
                   (fun uu____50450  ->
                      match uu____50450 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____50432 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____50490,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____50518 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____50537 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____50568) -> (n1, d, "interface")
       in
    match uu____50537 with
    | (name,decls,_mt) ->
        let uu____50588 = one_toplevel decls  in
        (match uu____50588 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____50625 = document_toplevel name top_decl  in
             (match uu____50625 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____50665 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____50665);
                   (let uu____50671 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____50671);
                   (let uu____50677 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____50677);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____50690 =
               let uu____50696 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____50696)  in
             FStar_Errors.raise_err uu____50690)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____50720 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____50720) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____50750 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____50750) mods;
    FStar_Util.close_file fd
  