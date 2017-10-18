open Prims
let one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun decls  ->
    let uu____17 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____29 -> true
           | uu____30 -> false) decls
       in
    match uu____17 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____66 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 
  | Branch of mforest FStar_Util.smap [@@deriving show]
let uu___is_Leaf : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____98 -> false
  
let __proj__Leaf__item___0 :
  mforest -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let uu___is_Branch : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____126 -> false
  
let __proj__Branch__item___0 : mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let htree : mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____153 'Auu____154 .
    ('Auu____154 -> 'Auu____153) ->
      'Auu____153 ->
        'Auu____154 FStar_Pervasives_Native.option -> 'Auu____153
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
         let uu____228 =
           let uu____229 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat uu____229 "*)"  in
         Prims.strcat "(*" uu____228) "" d
  
let string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let code_wrap : Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let string_of_tycon : FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____246 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____257 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id,_bb,_ko,fields) ->
        let uu____302 =
          let uu____303 =
            let uu____304 =
              let uu____305 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____344  ->
                        match uu____344 with
                        | (id1,t,doco) ->
                            let uu____390 = string_of_fsdoco doco  in
                            let uu____391 =
                              let uu____392 =
                                let uu____393 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" uu____393  in
                              Prims.strcat id1.FStar_Ident.idText uu____392
                               in
                            Prims.strcat uu____390 uu____391))
                 in
              FStar_All.pipe_right uu____305 (FStar_String.concat "; ")  in
            Prims.strcat uu____304 " }"  in
          Prims.strcat " = { " uu____303  in
        Prims.strcat id.FStar_Ident.idText uu____302
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____436 =
          let uu____437 =
            let uu____438 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____486  ->
                      match uu____486 with
                      | (id1,trmo,doco,u) ->
                          let uu____541 = string_of_fsdoco doco  in
                          let uu____542 =
                            let uu____543 =
                              let uu____544 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" uu____544  in
                            Prims.strcat id1.FStar_Ident.idText uu____543  in
                          Prims.strcat uu____541 uu____542))
               in
            FStar_All.pipe_right uu____438 (FStar_String.concat " | ")  in
          Prims.strcat " = " uu____437  in
        Prims.strcat id.FStar_Ident.idText uu____436
  
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
    | FStar_Parser_AST.TopLevelLet (uu____556,pats) ->
        let termty =
          FStar_List.map
            (fun uu____590  ->
               match uu____590 with
               | (p,t) ->
                   let uu____601 = FStar_Parser_AST.pat_to_string p  in
                   let uu____602 = FStar_Parser_AST.term_to_string t  in
                   (uu____601, uu____602)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____613  ->
               match uu____613 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____620 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____623 =
          let uu____624 =
            let uu____625 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____625  in
          Prims.strcat i.FStar_Ident.idText uu____624  in
        Prims.strcat "assume " uu____623
    | FStar_Parser_AST.Tycon (uu____626,tys) ->
        let uu____644 =
          let uu____645 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____679  ->
                    match uu____679 with
                    | (t,d1) ->
                        let uu____722 = string_of_tycon t  in
                        let uu____723 =
                          let uu____724 = string_of_fsdoco d1  in
                          Prims.strcat " " uu____724  in
                        Prims.strcat uu____722 uu____723))
             in
          FStar_All.pipe_right uu____645 (FStar_String.concat " and ")  in
        Prims.strcat "type " uu____644
    | FStar_Parser_AST.Val (i,t) ->
        let uu____729 =
          let uu____730 =
            let uu____731 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____731  in
          Prims.strcat i.FStar_Ident.idText uu____730  in
        Prims.strcat "val " uu____729
    | FStar_Parser_AST.Exception (i,uu____733) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____739,uu____740,uu____741)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____751,uu____752)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____757 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____758 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____760) -> comm
  
let decl_documented : FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____801 -> false
        | FStar_Parser_AST.TyconAbbrev uu____812 -> false
        | FStar_Parser_AST.TyconRecord (uu____825,uu____826,uu____827,fields)
            ->
            FStar_List.existsb
              (fun uu____869  ->
                 match uu____869 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____885,uu____886,uu____887,vars)
            ->
            FStar_List.existsb
              (fun uu____942  ->
                 match uu____942 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____976  ->
           match uu____976 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____989 -> true
    | uu____990 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____993 -> true
         | FStar_Parser_AST.Tycon (uu____994,ty) -> tycon_documented ty
         | uu____1012 -> false)
  
let document_decl :
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1026 = d  in
        match uu____1026 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1028;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1030;
            FStar_Parser_AST.attrs = uu____1031;_} ->
            ((let uu____1035 =
                let uu____1036 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____1036  in
              w uu____1035);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1062 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____1072 .
    'Auu____1072 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1089 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____1122 =
                 FStar_List.tryFind
                   (fun uu____1136  ->
                      match uu____1136 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____1122 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1159,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1173 ->
          FStar_Exn.raise (FStar_Errors.Err "Not a TopLevelModule")
  
let document_module : FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____1186 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1213) -> (n1, d, "interface")
       in
    match uu____1186 with
    | (name,decls,_mt) ->
        let uu____1227 = one_toplevel decls  in
        (match uu____1227 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____1255 = document_toplevel name top_decl  in
             (match uu____1255 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____1279 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____1279);
                   (let uu____1281 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____1281);
                   (let uu____1283 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____1283);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____1292 =
               let uu____1293 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               FStar_Errors.Err uu____1293  in
             FStar_Exn.raise uu____1292)
  
let generate : Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____1308 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____1308) files
       in
    let mods = FStar_List.map document_module modules  in
    let on = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on  in
    FStar_List.iter
      (fun m  ->
         let uu____1334 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____1334) mods;
    FStar_Util.close_file fd
  