open Prims
let one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option
  =
  fun decls  ->
    let uu____10 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____16 -> true
           | uu____17 -> false) decls
       in
    match uu____10 with
    | (top,nontops) ->
        (match top with | t::[] -> Some (t, nontops) | uu____37 -> None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let uu___is_Leaf : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____57 -> false
  
let __proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let uu___is_Branch : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____76 -> false
  
let __proj__Branch__item___0 : mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let htree : mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont f y xo = match xo with | Some x -> f x | None  -> y 
let string_of_fsdoco :
  (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option ->
    Prims.string
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let _0_642 =
           let _0_641 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat _0_641 "*)"  in
         Prims.strcat "(*" _0_642) "" d
  
let string_of_termo : FStar_Parser_AST.term Prims.option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let code_wrap : Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let string_of_tycon : FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____154 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____160 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id,_bb,_ko,fields) ->
        let uu____185 =
          let uu____186 =
            let uu____187 =
              let uu____188 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____199  ->
                        match uu____199 with
                        | (id,t,doco) ->
                            let _0_646 = string_of_fsdoco doco  in
                            let _0_645 =
                              let _0_644 =
                                let _0_643 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" _0_643  in
                              Prims.strcat id.FStar_Ident.idText _0_644  in
                            Prims.strcat _0_646 _0_645))
                 in
              FStar_All.pipe_right _0_647 (FStar_String.concat "; ")  in
            Prims.strcat _0_648 " }"  in
          Prims.strcat " = { " _0_649  in
        Prims.strcat id.FStar_Ident.idText _0_650
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____257 =
          let uu____258 =
            let uu____259 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____266  ->
                      match uu____266 with
                      | (id,trmo,doco,u) ->
                          let _0_654 = string_of_fsdoco doco  in
                          let _0_653 =
                            let _0_652 =
                              let _0_651 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" _0_651  in
                            Prims.strcat id.FStar_Ident.idText _0_652  in
                          Prims.strcat _0_654 _0_653))
               in
            FStar_All.pipe_right _0_655 (FStar_String.concat " | ")  in
          Prims.strcat " = " _0_656  in
        Prims.strcat id.FStar_Ident.idText _0_657
  
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
    | FStar_Parser_AST.TopLevelLet (uu____323,pats) ->
        let termty =
          FStar_List.map
            (fun uu____339  ->
               match uu____339 with
               | (p,t) ->
                   let _0_659 = FStar_Parser_AST.pat_to_string p  in
                   let _0_658 = FStar_Parser_AST.term_to_string t  in
                   (_0_659, _0_658)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____331  ->
               match uu____331 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____357 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let _0_662 =
          let _0_661 =
            let _0_660 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" _0_660  in
          Prims.strcat i.FStar_Ident.idText _0_661  in
        Prims.strcat "assume " _0_662
    | FStar_Parser_AST.Tycon (uu____339,tys) ->
        let _0_667 =
          let _0_666 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____363  ->
                    match uu____363 with
                    | (t,d) ->
                        let _0_665 = string_of_tycon t  in
                        let _0_664 =
                          let _0_663 = string_of_fsdoco d  in
                          Prims.strcat " " _0_663  in
                        Prims.strcat _0_665 _0_664))
             in
          FStar_All.pipe_right _0_666 (FStar_String.concat " and ")  in
        Prims.strcat "type " _0_667
    | FStar_Parser_AST.Val (i,t) ->
        let _0_670 =
          let _0_669 =
            let _0_668 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" _0_668  in
          Prims.strcat i.FStar_Ident.idText _0_669  in
        Prims.strcat "val " _0_670
    | FStar_Parser_AST.Exception (i,uu____389) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i,_,_,_))
      |FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i,_,_))
        -> Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect
      (i,_,_,_,_))|FStar_Parser_AST.NewEffectForFree
      (FStar_Parser_AST.RedefineEffect (i,_,_)) ->
        Prims.strcat "new_effect_for_free " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____414 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____415 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____417) -> comm
  
let decl_documented : FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract _|FStar_Parser_AST.TyconAbbrev _ ->
            false
        | FStar_Parser_AST.TyconRecord (uu____465,uu____466,uu____467,fields)
            ->
            FStar_List.existsb
              (fun uu____487  ->
                 match uu____487 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____497,uu____498,uu____499,vars)
            ->
            FStar_List.existsb
              (fun uu____505  ->
                 match uu____505 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____543  ->
           match uu____543 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | Some uu____551 -> true
    | uu____552 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____534 -> true
         | FStar_Parser_AST.Tycon (uu____535,ty) -> tycon_documented ty
         | uu____545 -> false)
  
let document_decl :
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      match decl_documented d with
      | true  ->
          let uu____557 = d  in
          (match uu____557 with
           | { FStar_Parser_AST.d = decl;
               FStar_Parser_AST.drange = uu____559;
               FStar_Parser_AST.doc = fsdoc;
               FStar_Parser_AST.quals = uu____561;
               FStar_Parser_AST.attrs = uu____562;_} ->
               (w (code_wrap (string_of_decl' d.FStar_Parser_AST.d));
                (match fsdoc with
                 | Some (doc,_kw) -> w (Prims.strcat "\n" doc)
                 | uu____579 -> ());
                w ""))
      | uu____581 -> ()
  
let document_toplevel name topdecl =
  match topdecl.FStar_Parser_AST.d with
  | FStar_Parser_AST.TopLevelModule uu____620 ->
      (match topdecl.FStar_Parser_AST.doc with
       | Some (doc1,kw) ->
           let uu____638 =
             FStar_List.tryFind
               (fun uu____622  ->
                  match uu____622 with | (k,v) -> k = "summary") kw
              in
           (match uu____616 with
            | None  -> (None, (Some doc))
            | Some (uu____635,summary) -> ((Some summary), (Some doc)))
       | None  -> (None, None))
  | uu____643 -> Prims.raise (FStar_Errors.Err "Not a TopLevelModule") 
let document_module : FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____673 =
      match m with
      | FStar_Parser_AST.Module (n,d) -> (n, d, "module")
      | FStar_Parser_AST.Interface (n,d,uu____667) -> (n, d, "interface")  in
    match uu____651 with
    | (name,decls,_mt) ->
        let uu____676 = one_toplevel decls  in
        (match uu____676 with
         | Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____695 = document_toplevel name top_decl  in
             (match uu____695 with
              | (summary,comment) ->
                  let summary =
                    match summary with | Some s -> s | None  -> no_summary
                     in
                  let comment =
                    match comment with | Some s -> s | None  -> no_comment
                     in
                  (w (FStar_Util.format "# module %s" [name.FStar_Ident.str]);
                   w (FStar_Util.format "%s\n" [summary]);
                   w (FStar_Util.format "%s\n" [comment]);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | None  ->
             Prims.raise
               (FStar_Errors.Err
                  (FStar_Util.format1 "No singleton toplevel in module %s"
                     name.FStar_Ident.str)))
  
let generate : Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.collect
        (fun fn  -> Prims.fst (FStar_Parser_Driver.parse_file fn)) files
       in
    let mods = FStar_List.map document_module modules  in
    let on = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on  in
    FStar_List.iter
      (fun m  ->
         let _0_671 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd _0_671) mods;
    FStar_Util.close_file fd
  