open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____49707 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____49720 -> true
           | uu____49722 -> false) decls
       in
    match uu____49707 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____49759 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____49802 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____49842 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____49873 'Auu____49874 .
    ('Auu____49873 -> 'Auu____49874) ->
      'Auu____49874 ->
        'Auu____49873 FStar_Pervasives_Native.option -> 'Auu____49874
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
         let uu____49967 =
           let uu____49969 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____49969 "*)"  in
         Prims.op_Hat "(*" uu____49967) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____50006 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____50018 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____50064 =
          let uu____50066 =
            let uu____50068 =
              let uu____50070 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____50128  ->
                        match uu____50128 with
                        | (id2,t,doco) ->
                            let uu____50184 = string_of_fsdoco doco  in
                            let uu____50186 =
                              let uu____50188 =
                                let uu____50190 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____50190  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____50188
                               in
                            Prims.op_Hat uu____50184 uu____50186))
                 in
              FStar_All.pipe_right uu____50070 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____50068 " }"  in
          Prims.op_Hat " = { " uu____50066  in
        Prims.op_Hat id1.FStar_Ident.idText uu____50064
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____50242 =
          let uu____50244 =
            let uu____50246 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____50315  ->
                      match uu____50315 with
                      | (id2,trmo,doco,u) ->
                          let uu____50383 = string_of_fsdoco doco  in
                          let uu____50385 =
                            let uu____50387 =
                              let uu____50389 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____50389  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____50387
                             in
                          Prims.op_Hat uu____50383 uu____50385))
               in
            FStar_All.pipe_right uu____50246 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____50244  in
        Prims.op_Hat id1.FStar_Ident.idText uu____50242
  
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
    | FStar_Parser_AST.TopLevelLet (uu____50420,pats) ->
        let termty =
          FStar_List.map
            (fun uu____50458  ->
               match uu____50458 with
               | (p,t) ->
                   let uu____50471 = FStar_Parser_AST.pat_to_string p  in
                   let uu____50473 = FStar_Parser_AST.term_to_string t  in
                   (uu____50471, uu____50473)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____50491  ->
               match uu____50491 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____50508 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____50512 =
          let uu____50514 =
            let uu____50516 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____50516  in
          Prims.op_Hat i.FStar_Ident.idText uu____50514  in
        Prims.op_Hat "assume " uu____50512
    | FStar_Parser_AST.Tycon (uu____50520,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____50551 =
          let uu____50553 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____50606  ->
                    match uu____50606 with
                    | (t,d1) ->
                        let uu____50659 = string_of_tycon t  in
                        let uu____50661 =
                          let uu____50663 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____50663  in
                        Prims.op_Hat uu____50659 uu____50661))
             in
          FStar_All.pipe_right uu____50553 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____50551
    | FStar_Parser_AST.Val (i,t) ->
        let uu____50673 =
          let uu____50675 =
            let uu____50677 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____50677  in
          Prims.op_Hat i.FStar_Ident.idText uu____50675  in
        Prims.op_Hat "val " uu____50673
    | FStar_Parser_AST.Exception (i,uu____50682) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____50689,uu____50690,uu____50691)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____50702,uu____50703)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____50709 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____50711 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____50719 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____50719
    | FStar_Parser_AST.Fsdoc (comm,uu____50723) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____50780 -> false
        | FStar_Parser_AST.TyconAbbrev uu____50792 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____50806,uu____50807,uu____50808,fields) ->
            FStar_List.existsb
              (fun uu____50850  ->
                 match uu____50850 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____50867,uu____50868,uu____50869,vars) ->
            FStar_List.existsb
              (fun uu____50927  ->
                 match uu____50927 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____50965  ->
           match uu____50965 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____50980 -> true
    | uu____50982 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____50986 -> true
         | FStar_Parser_AST.Tycon (uu____50988,uu____50989,ty) ->
             tycon_documented ty
         | uu____51011 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____51032 = d  in
        match uu____51032 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____51034;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____51036;
            FStar_Parser_AST.attrs = uu____51037;_} ->
            ((let uu____51041 =
                let uu____51043 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____51043  in
              w uu____51041);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____51067 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____51080 .
    'Auu____51080 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____51101 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____51132 =
                 FStar_List.tryFind
                   (fun uu____51150  ->
                      match uu____51150 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____51132 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____51190,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____51218 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____51237 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____51268) -> (n1, d, "interface")
       in
    match uu____51237 with
    | (name,decls,_mt) ->
        let uu____51288 = one_toplevel decls  in
        (match uu____51288 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____51325 = document_toplevel name top_decl  in
             (match uu____51325 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____51365 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____51365);
                   (let uu____51371 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____51371);
                   (let uu____51377 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____51377);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____51390 =
               let uu____51396 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____51396)  in
             FStar_Errors.raise_err uu____51390)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____51420 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____51420) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____51450 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____51450) mods;
    FStar_Util.close_file fd
  