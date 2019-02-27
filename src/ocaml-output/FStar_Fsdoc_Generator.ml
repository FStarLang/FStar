open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____53605 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____53618 -> true
           | uu____53620 -> false) decls
       in
    match uu____53605 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____53657 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____53700 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____53740 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____53771 'Auu____53772 .
    ('Auu____53771 -> 'Auu____53772) ->
      'Auu____53772 ->
        'Auu____53771 FStar_Pervasives_Native.option -> 'Auu____53772
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
         let uu____53865 =
           let uu____53867 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____53867 "*)"  in
         Prims.op_Hat "(*" uu____53865) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____53904 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____53916 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____53962 =
          let uu____53964 =
            let uu____53966 =
              let uu____53968 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____54026  ->
                        match uu____54026 with
                        | (id2,t,doco) ->
                            let uu____54082 = string_of_fsdoco doco  in
                            let uu____54084 =
                              let uu____54086 =
                                let uu____54088 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____54088  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____54086
                               in
                            Prims.op_Hat uu____54082 uu____54084))
                 in
              FStar_All.pipe_right uu____53968 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____53966 " }"  in
          Prims.op_Hat " = { " uu____53964  in
        Prims.op_Hat id1.FStar_Ident.idText uu____53962
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____54140 =
          let uu____54142 =
            let uu____54144 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____54213  ->
                      match uu____54213 with
                      | (id2,trmo,doco,u) ->
                          let uu____54281 = string_of_fsdoco doco  in
                          let uu____54283 =
                            let uu____54285 =
                              let uu____54287 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____54287  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____54285
                             in
                          Prims.op_Hat uu____54281 uu____54283))
               in
            FStar_All.pipe_right uu____54144 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____54142  in
        Prims.op_Hat id1.FStar_Ident.idText uu____54140
  
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
    | FStar_Parser_AST.TopLevelLet (uu____54318,pats) ->
        let termty =
          FStar_List.map
            (fun uu____54356  ->
               match uu____54356 with
               | (p,t) ->
                   let uu____54369 = FStar_Parser_AST.pat_to_string p  in
                   let uu____54371 = FStar_Parser_AST.term_to_string t  in
                   (uu____54369, uu____54371)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____54389  ->
               match uu____54389 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____54406 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____54410 =
          let uu____54412 =
            let uu____54414 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54414  in
          Prims.op_Hat i.FStar_Ident.idText uu____54412  in
        Prims.op_Hat "assume " uu____54410
    | FStar_Parser_AST.Tycon (uu____54418,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____54449 =
          let uu____54451 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____54504  ->
                    match uu____54504 with
                    | (t,d1) ->
                        let uu____54557 = string_of_tycon t  in
                        let uu____54559 =
                          let uu____54561 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____54561  in
                        Prims.op_Hat uu____54557 uu____54559))
             in
          FStar_All.pipe_right uu____54451 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____54449
    | FStar_Parser_AST.Val (i,t) ->
        let uu____54571 =
          let uu____54573 =
            let uu____54575 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54575  in
          Prims.op_Hat i.FStar_Ident.idText uu____54573  in
        Prims.op_Hat "val " uu____54571
    | FStar_Parser_AST.Exception (i,uu____54580) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____54587,uu____54588,uu____54589)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____54600,uu____54601)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____54607 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____54609 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____54617 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____54617
    | FStar_Parser_AST.Fsdoc (comm,uu____54621) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____54678 -> false
        | FStar_Parser_AST.TyconAbbrev uu____54690 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____54704,uu____54705,uu____54706,fields) ->
            FStar_List.existsb
              (fun uu____54748  ->
                 match uu____54748 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____54765,uu____54766,uu____54767,vars) ->
            FStar_List.existsb
              (fun uu____54825  ->
                 match uu____54825 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____54863  ->
           match uu____54863 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____54878 -> true
    | uu____54880 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54884 -> true
         | FStar_Parser_AST.Tycon (uu____54886,uu____54887,ty) ->
             tycon_documented ty
         | uu____54909 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____54930 = d  in
        match uu____54930 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____54932;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____54934;
            FStar_Parser_AST.attrs = uu____54935;_} ->
            ((let uu____54939 =
                let uu____54941 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____54941  in
              w uu____54939);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____54965 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____54978 .
    'Auu____54978 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____54999 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____55030 =
                 FStar_List.tryFind
                   (fun uu____55048  ->
                      match uu____55048 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____55030 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____55088,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____55116 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____55135 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____55166) -> (n1, d, "interface")
       in
    match uu____55135 with
    | (name,decls,_mt) ->
        let uu____55186 = one_toplevel decls  in
        (match uu____55186 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____55223 = document_toplevel name top_decl  in
             (match uu____55223 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____55263 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____55263);
                   (let uu____55269 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____55269);
                   (let uu____55275 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____55275);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____55288 =
               let uu____55294 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____55294)  in
             FStar_Errors.raise_err uu____55288)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____55318 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____55318) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____55348 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____55348) mods;
    FStar_Util.close_file fd
  