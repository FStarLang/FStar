open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____53610 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____53623 -> true
           | uu____53625 -> false) decls
       in
    match uu____53610 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____53662 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____53705 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____53745 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____53776 'Auu____53777 .
    ('Auu____53776 -> 'Auu____53777) ->
      'Auu____53777 ->
        'Auu____53776 FStar_Pervasives_Native.option -> 'Auu____53777
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
         let uu____53870 =
           let uu____53872 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____53872 "*)"  in
         Prims.op_Hat "(*" uu____53870) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____53909 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____53921 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____53967 =
          let uu____53969 =
            let uu____53971 =
              let uu____53973 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____54031  ->
                        match uu____54031 with
                        | (id2,t,doco) ->
                            let uu____54087 = string_of_fsdoco doco  in
                            let uu____54089 =
                              let uu____54091 =
                                let uu____54093 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____54093  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____54091
                               in
                            Prims.op_Hat uu____54087 uu____54089))
                 in
              FStar_All.pipe_right uu____53973 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____53971 " }"  in
          Prims.op_Hat " = { " uu____53969  in
        Prims.op_Hat id1.FStar_Ident.idText uu____53967
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____54145 =
          let uu____54147 =
            let uu____54149 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____54218  ->
                      match uu____54218 with
                      | (id2,trmo,doco,u) ->
                          let uu____54286 = string_of_fsdoco doco  in
                          let uu____54288 =
                            let uu____54290 =
                              let uu____54292 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____54292  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____54290
                             in
                          Prims.op_Hat uu____54286 uu____54288))
               in
            FStar_All.pipe_right uu____54149 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____54147  in
        Prims.op_Hat id1.FStar_Ident.idText uu____54145
  
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
    | FStar_Parser_AST.TopLevelLet (uu____54323,pats) ->
        let termty =
          FStar_List.map
            (fun uu____54361  ->
               match uu____54361 with
               | (p,t) ->
                   let uu____54374 = FStar_Parser_AST.pat_to_string p  in
                   let uu____54376 = FStar_Parser_AST.term_to_string t  in
                   (uu____54374, uu____54376)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____54394  ->
               match uu____54394 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____54411 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____54415 =
          let uu____54417 =
            let uu____54419 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54419  in
          Prims.op_Hat i.FStar_Ident.idText uu____54417  in
        Prims.op_Hat "assume " uu____54415
    | FStar_Parser_AST.Tycon (uu____54423,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____54454 =
          let uu____54456 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____54509  ->
                    match uu____54509 with
                    | (t,d1) ->
                        let uu____54562 = string_of_tycon t  in
                        let uu____54564 =
                          let uu____54566 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____54566  in
                        Prims.op_Hat uu____54562 uu____54564))
             in
          FStar_All.pipe_right uu____54456 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____54454
    | FStar_Parser_AST.Val (i,t) ->
        let uu____54576 =
          let uu____54578 =
            let uu____54580 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54580  in
          Prims.op_Hat i.FStar_Ident.idText uu____54578  in
        Prims.op_Hat "val " uu____54576
    | FStar_Parser_AST.Exception (i,uu____54585) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____54592,uu____54593,uu____54594)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____54605,uu____54606)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____54612 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____54614 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____54622 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____54622
    | FStar_Parser_AST.Fsdoc (comm,uu____54626) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____54683 -> false
        | FStar_Parser_AST.TyconAbbrev uu____54695 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____54709,uu____54710,uu____54711,fields) ->
            FStar_List.existsb
              (fun uu____54753  ->
                 match uu____54753 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____54770,uu____54771,uu____54772,vars) ->
            FStar_List.existsb
              (fun uu____54830  ->
                 match uu____54830 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____54868  ->
           match uu____54868 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____54883 -> true
    | uu____54885 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54889 -> true
         | FStar_Parser_AST.Tycon (uu____54891,uu____54892,ty) ->
             tycon_documented ty
         | uu____54914 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____54935 = d  in
        match uu____54935 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____54937;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____54939;
            FStar_Parser_AST.attrs = uu____54940;_} ->
            ((let uu____54944 =
                let uu____54946 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____54946  in
              w uu____54944);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____54970 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____54983 .
    'Auu____54983 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____55004 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____55035 =
                 FStar_List.tryFind
                   (fun uu____55053  ->
                      match uu____55053 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____55035 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____55093,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____55121 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____55140 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____55171) -> (n1, d, "interface")
       in
    match uu____55140 with
    | (name,decls,_mt) ->
        let uu____55191 = one_toplevel decls  in
        (match uu____55191 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____55228 = document_toplevel name top_decl  in
             (match uu____55228 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____55268 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____55268);
                   (let uu____55274 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____55274);
                   (let uu____55280 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____55280);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____55293 =
               let uu____55299 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____55299)  in
             FStar_Errors.raise_err uu____55293)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____55323 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____55323) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____55353 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____55353) mods;
    FStar_Util.close_file fd
  