open Prims
let one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
let uu___is_Leaf : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____102 -> false
  
let __proj__Leaf__item___0 :
  mforest -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let uu___is_Branch : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____130 -> false
  
let __proj__Branch__item___0 : mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let htree : mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.lift_native_int (50)) 
let string_of_optiont :
  'Auu____156 'Auu____157 .
    ('Auu____156 -> 'Auu____157) ->
      'Auu____157 ->
        'Auu____156 FStar_Pervasives_Native.option -> 'Auu____157
  =
  fun f  ->
    fun y  ->
      fun xo  ->
        match xo with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> y
  
let string_of_fsdoco :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
    Prims.string
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____235 =
           let uu____236 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat uu____236 "*)"  in
         Prims.strcat "(*" uu____235) "" d
  
let string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let code_wrap : Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let string_of_tycon : FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____256 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____267 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____312 =
          let uu____313 =
            let uu____314 =
              let uu____315 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____354  ->
                        match uu____354 with
                        | (id2,t,doco) ->
                            let uu____400 = string_of_fsdoco doco  in
                            let uu____401 =
                              let uu____402 =
                                let uu____403 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" uu____403  in
                              Prims.strcat id2.FStar_Ident.idText uu____402
                               in
                            Prims.strcat uu____400 uu____401))
                 in
              FStar_All.pipe_right uu____315 (FStar_String.concat "; ")  in
            Prims.strcat uu____314 " }"  in
          Prims.strcat " = { " uu____313  in
        Prims.strcat id1.FStar_Ident.idText uu____312
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____446 =
          let uu____447 =
            let uu____448 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____496  ->
                      match uu____496 with
                      | (id2,trmo,doco,u) ->
                          let uu____551 = string_of_fsdoco doco  in
                          let uu____552 =
                            let uu____553 =
                              let uu____554 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" uu____554  in
                            Prims.strcat id2.FStar_Ident.idText uu____553  in
                          Prims.strcat uu____551 uu____552))
               in
            FStar_All.pipe_right uu____448 (FStar_String.concat " | ")  in
          Prims.strcat " = " uu____447  in
        Prims.strcat id1.FStar_Ident.idText uu____446
  
let string_of_decl' : FStar_Parser_AST.decl' -> Prims.string =
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
    | FStar_Parser_AST.TopLevelLet (uu____567,pats) ->
        let termty =
          FStar_List.map
            (fun uu____601  ->
               match uu____601 with
               | (p,t) ->
                   let uu____612 = FStar_Parser_AST.pat_to_string p  in
                   let uu____613 = FStar_Parser_AST.term_to_string t  in
                   (uu____612, uu____613)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____624  ->
               match uu____624 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____631 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____634 =
          let uu____635 =
            let uu____636 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____636  in
          Prims.strcat i.FStar_Ident.idText uu____635  in
        Prims.strcat "assume " uu____634
    | FStar_Parser_AST.Tycon (uu____637,tys) ->
        let uu____655 =
          let uu____656 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____690  ->
                    match uu____690 with
                    | (t,d1) ->
                        let uu____733 = string_of_tycon t  in
                        let uu____734 =
                          let uu____735 = string_of_fsdoco d1  in
                          Prims.strcat " " uu____735  in
                        Prims.strcat uu____733 uu____734))
             in
          FStar_All.pipe_right uu____656 (FStar_String.concat " and ")  in
        Prims.strcat "type " uu____655
    | FStar_Parser_AST.Val (i,t) ->
        let uu____740 =
          let uu____741 =
            let uu____742 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____742  in
          Prims.strcat i.FStar_Ident.idText uu____741  in
        Prims.strcat "val " uu____740
    | FStar_Parser_AST.Exception (i,uu____744) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____750,uu____751,uu____752)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____762,uu____763)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____768 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____769 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____776 = FStar_Parser_AST.term_to_string t  in
        Prims.strcat "splice " uu____776
    | FStar_Parser_AST.Fsdoc (comm,uu____778) -> comm
  
let decl_documented : FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____824 -> false
        | FStar_Parser_AST.TyconAbbrev uu____835 -> false
        | FStar_Parser_AST.TyconRecord (uu____848,uu____849,uu____850,fields)
            ->
            FStar_List.existsb
              (fun uu____892  ->
                 match uu____892 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____908,uu____909,uu____910,vars)
            ->
            FStar_List.existsb
              (fun uu____965  ->
                 match uu____965 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____999  ->
           match uu____999 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____1012 -> true
    | uu____1013 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____1016 -> true
         | FStar_Parser_AST.Tycon (uu____1017,ty) -> tycon_documented ty
         | uu____1035 -> false)
  
let document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1051 = d  in
        match uu____1051 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1053;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1055;
            FStar_Parser_AST.attrs = uu____1056;_} ->
            ((let uu____1060 =
                let uu____1061 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____1061  in
              w uu____1060);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1087 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____1097 .
    'Auu____1097 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1116 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____1149 =
                 FStar_List.tryFind
                   (fun uu____1163  ->
                      match uu____1163 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____1149 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1186,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1200 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let document_module : FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____1214 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1241) -> (n1, d, "interface")
       in
    match uu____1214 with
    | (name,decls,_mt) ->
        let uu____1255 = one_toplevel decls  in
        (match uu____1255 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____1285 = document_toplevel name top_decl  in
             (match uu____1285 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____1309 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____1309);
                   (let uu____1311 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____1311);
                   (let uu____1313 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____1313);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____1322 =
               let uu____1327 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____1327)  in
             FStar_Errors.raise_err uu____1322)
  
let generate : Prims.string Prims.list -> unit =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____1343 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____1343) files
       in
    let mods = FStar_List.map document_module modules  in
    let on = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on  in
    FStar_List.iter
      (fun m  ->
         let uu____1369 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____1369) mods;
    FStar_Util.close_file fd
  