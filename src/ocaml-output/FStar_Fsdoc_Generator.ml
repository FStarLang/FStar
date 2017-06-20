open Prims
let one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) option
  =
  fun decls  ->
    let uu____11 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____17 -> true
           | uu____18 -> false) decls
       in
    match uu____11 with
    | (top,nontops) ->
        (match top with | t::[] -> Some (t, nontops) | uu____38 -> None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let uu___is_Leaf : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____61 -> false
  
let __proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let uu___is_Branch : mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____82 -> false
  
let __proj__Branch__item___0 : mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let htree : mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont f y xo = match xo with | Some x -> f x | None  -> y 
let string_of_fsdoco :
  (Prims.string * (Prims.string * Prims.string) Prims.list) option ->
    Prims.string
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____154 =
           let uu____155 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat uu____155 "*)"  in
         Prims.strcat "(*" uu____154) "" d
  
let string_of_termo : FStar_Parser_AST.term option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let code_wrap : Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let string_of_tycon : FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____170 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____176 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id,_bb,_ko,fields) ->
        let uu____201 =
          let uu____202 =
            let uu____203 =
              let uu____204 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____221  ->
                        match uu____221 with
                        | (id1,t,doco) ->
                            let uu____246 = string_of_fsdoco doco  in
                            let uu____247 =
                              let uu____248 =
                                let uu____249 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" uu____249  in
                              Prims.strcat id1.FStar_Ident.idText uu____248
                               in
                            Prims.strcat uu____246 uu____247))
                 in
              FStar_All.pipe_right uu____204 (FStar_String.concat "; ")  in
            Prims.strcat uu____203 " }"  in
          Prims.strcat " = { " uu____202  in
        Prims.strcat id.FStar_Ident.idText uu____201
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____273 =
          let uu____274 =
            let uu____275 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____296  ->
                      match uu____296 with
                      | (id1,trmo,doco,u) ->
                          let uu____326 = string_of_fsdoco doco  in
                          let uu____327 =
                            let uu____328 =
                              let uu____329 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" uu____329  in
                            Prims.strcat id1.FStar_Ident.idText uu____328  in
                          Prims.strcat uu____326 uu____327))
               in
            FStar_All.pipe_right uu____275 (FStar_String.concat " | ")  in
          Prims.strcat " = " uu____274  in
        Prims.strcat id.FStar_Ident.idText uu____273
  
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
    | FStar_Parser_AST.TopLevelLet (uu____340,pats) ->
        let termty =
          FStar_List.map
            (fun uu____356  ->
               match uu____356 with
               | (p,t) ->
                   let uu____363 = FStar_Parser_AST.pat_to_string p  in
                   let uu____364 = FStar_Parser_AST.term_to_string t  in
                   (uu____363, uu____364)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____369  ->
               match uu____369 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____374 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____377 =
          let uu____378 =
            let uu____379 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____379  in
          Prims.strcat i.FStar_Ident.idText uu____378  in
        Prims.strcat "assume " uu____377
    | FStar_Parser_AST.Tycon (uu____380,tys) ->
        let uu____390 =
          let uu____391 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____406  ->
                    match uu____406 with
                    | (t,d1) ->
                        let uu____429 = string_of_tycon t  in
                        let uu____430 =
                          let uu____431 = string_of_fsdoco d1  in
                          Prims.strcat " " uu____431  in
                        Prims.strcat uu____429 uu____430))
             in
          FStar_All.pipe_right uu____391 (FStar_String.concat " and ")  in
        Prims.strcat "type " uu____390
    | FStar_Parser_AST.Val (i,t) ->
        let uu____435 =
          let uu____436 =
            let uu____437 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____437  in
          Prims.strcat i.FStar_Ident.idText uu____436  in
        Prims.strcat "val " uu____435
    | FStar_Parser_AST.Exception (i,uu____439) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____443,uu____444,uu____445)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____451,uu____452)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____455 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____456 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____458) -> comm
  
let decl_documented : FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____485 -> false
        | FStar_Parser_AST.TyconAbbrev uu____491 -> false
        | FStar_Parser_AST.TyconRecord (uu____498,uu____499,uu____500,fields)
            ->
            FStar_List.existsb
              (fun uu____520  ->
                 match uu____520 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____530,uu____531,uu____532,vars)
            ->
            FStar_List.existsb
              (fun uu____558  ->
                 match uu____558 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____576  ->
           match uu____576 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | Some uu____584 -> true
    | uu____585 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____587 -> true
         | FStar_Parser_AST.Tycon (uu____588,ty) -> tycon_documented ty
         | uu____598 -> false)
  
let document_decl :
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____612 = d  in
        match uu____612 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____614;
            FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____616;
            FStar_Parser_AST.attrs = uu____617;_} ->
            ((let uu____620 =
                let uu____621 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____621  in
              w uu____620);
             (match fsdoc with
              | Some (doc1,_kw) -> w (Prims.strcat "\n" doc1)
              | uu____636 -> ());
             w "")
      else ()
  
let document_toplevel name topdecl =
  match topdecl.FStar_Parser_AST.d with
  | FStar_Parser_AST.TopLevelModule uu____658 ->
      (match topdecl.FStar_Parser_AST.doc with
       | Some (doc1,kw) ->
           let uu____676 =
             FStar_List.tryFind
               (fun uu____682  ->
                  match uu____682 with | (k,v1) -> k = "summary") kw
              in
           (match uu____676 with
            | None  -> (None, (Some doc1))
            | Some (uu____695,summary) -> ((Some summary), (Some doc1)))
       | None  -> (None, None))
  | uu____703 -> raise (FStar_Errors.Err "Not a TopLevelModule") 
let document_module : FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____712 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____728) -> (n1, d, "interface")
       in
    match uu____712 with
    | (name,decls,_mt) ->
        let uu____737 = one_toplevel decls  in
        (match uu____737 with
         | Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____756 = document_toplevel name top_decl  in
             (match uu____756 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with | Some s -> s | None  -> no_summary
                     in
                  let comment1 =
                    match comment with | Some s -> s | None  -> no_comment
                     in
                  ((let uu____772 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____772);
                   (let uu____774 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____774);
                   (let uu____776 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____776);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | None  ->
             let uu____782 =
               let uu____783 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               FStar_Errors.Err uu____783  in
             raise uu____782)
  
let generate : Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.collect
        (fun fn  ->
           let uu____793 = FStar_Parser_Driver.parse_file fn  in
           fst uu____793) files
       in
    let mods = FStar_List.map document_module modules  in
    let on = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on  in
    FStar_List.iter
      (fun m  ->
         let uu____808 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____808) mods;
    FStar_Util.close_file fd
  