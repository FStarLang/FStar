open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____53536 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____53549 -> true
           | uu____53551 -> false) decls
       in
    match uu____53536 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____53588 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____53631 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____53671 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____53702 'Auu____53703 .
    ('Auu____53702 -> 'Auu____53703) ->
      'Auu____53703 ->
        'Auu____53702 FStar_Pervasives_Native.option -> 'Auu____53703
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
         let uu____53796 =
           let uu____53798 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____53798 "*)"  in
         Prims.op_Hat "(*" uu____53796) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____53835 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____53847 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____53893 =
          let uu____53895 =
            let uu____53897 =
              let uu____53899 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____53957  ->
                        match uu____53957 with
                        | (id2,t,doco) ->
                            let uu____54013 = string_of_fsdoco doco  in
                            let uu____54015 =
                              let uu____54017 =
                                let uu____54019 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____54019  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____54017
                               in
                            Prims.op_Hat uu____54013 uu____54015))
                 in
              FStar_All.pipe_right uu____53899 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____53897 " }"  in
          Prims.op_Hat " = { " uu____53895  in
        Prims.op_Hat id1.FStar_Ident.idText uu____53893
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____54071 =
          let uu____54073 =
            let uu____54075 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____54144  ->
                      match uu____54144 with
                      | (id2,trmo,doco,u) ->
                          let uu____54212 = string_of_fsdoco doco  in
                          let uu____54214 =
                            let uu____54216 =
                              let uu____54218 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____54218  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____54216
                             in
                          Prims.op_Hat uu____54212 uu____54214))
               in
            FStar_All.pipe_right uu____54075 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____54073  in
        Prims.op_Hat id1.FStar_Ident.idText uu____54071
  
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
    | FStar_Parser_AST.TopLevelLet (uu____54249,pats) ->
        let termty =
          FStar_List.map
            (fun uu____54287  ->
               match uu____54287 with
               | (p,t) ->
                   let uu____54300 = FStar_Parser_AST.pat_to_string p  in
                   let uu____54302 = FStar_Parser_AST.term_to_string t  in
                   (uu____54300, uu____54302)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____54320  ->
               match uu____54320 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____54337 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____54341 =
          let uu____54343 =
            let uu____54345 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54345  in
          Prims.op_Hat i.FStar_Ident.idText uu____54343  in
        Prims.op_Hat "assume " uu____54341
    | FStar_Parser_AST.Tycon (uu____54349,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____54380 =
          let uu____54382 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____54435  ->
                    match uu____54435 with
                    | (t,d1) ->
                        let uu____54488 = string_of_tycon t  in
                        let uu____54490 =
                          let uu____54492 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____54492  in
                        Prims.op_Hat uu____54488 uu____54490))
             in
          FStar_All.pipe_right uu____54382 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____54380
    | FStar_Parser_AST.Val (i,t) ->
        let uu____54502 =
          let uu____54504 =
            let uu____54506 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54506  in
          Prims.op_Hat i.FStar_Ident.idText uu____54504  in
        Prims.op_Hat "val " uu____54502
    | FStar_Parser_AST.Exception (i,uu____54511) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____54518,uu____54519,uu____54520)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____54531,uu____54532)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____54538 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____54540 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____54548 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____54548
    | FStar_Parser_AST.Fsdoc (comm,uu____54552) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____54609 -> false
        | FStar_Parser_AST.TyconAbbrev uu____54621 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____54635,uu____54636,uu____54637,fields) ->
            FStar_List.existsb
              (fun uu____54679  ->
                 match uu____54679 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____54696,uu____54697,uu____54698,vars) ->
            FStar_List.existsb
              (fun uu____54756  ->
                 match uu____54756 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____54794  ->
           match uu____54794 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____54809 -> true
    | uu____54811 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54815 -> true
         | FStar_Parser_AST.Tycon (uu____54817,uu____54818,ty) ->
             tycon_documented ty
         | uu____54840 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____54861 = d  in
        match uu____54861 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____54863;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____54865;
            FStar_Parser_AST.attrs = uu____54866;_} ->
            ((let uu____54870 =
                let uu____54872 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____54872  in
              w uu____54870);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____54896 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____54909 .
    'Auu____54909 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____54930 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____54961 =
                 FStar_List.tryFind
                   (fun uu____54979  ->
                      match uu____54979 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____54961 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____55019,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____55047 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____55066 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____55097) -> (n1, d, "interface")
       in
    match uu____55066 with
    | (name,decls,_mt) ->
        let uu____55117 = one_toplevel decls  in
        (match uu____55117 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____55154 = document_toplevel name top_decl  in
             (match uu____55154 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____55194 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____55194);
                   (let uu____55200 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____55200);
                   (let uu____55206 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____55206);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____55219 =
               let uu____55225 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____55225)  in
             FStar_Errors.raise_err uu____55219)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____55249 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____55249) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____55279 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____55279) mods;
    FStar_Util.close_file fd
  