open Prims
let one_toplevel:
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl* FStar_Parser_AST.decl Prims.list) Prims.option
  =
  fun decls  ->
    let uu____10 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____16 -> true
           | uu____17 -> false) decls in
    match uu____10 with
    | (top,nontops) ->
        (match top with | t::[] -> Some (t, nontops) | uu____37 -> None)
type mforest =
  | Leaf of (Prims.string* Prims.string)
  | Branch of mforest FStar_Util.smap
let uu___is_Leaf: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____57 -> false
let __proj__Leaf__item___0: mforest -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | Leaf _0 -> _0
let uu___is_Branch: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____76 -> false
let __proj__Branch__item___0: mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0
let htree: mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50")
let string_of_optiont f y xo = match xo with | Some x -> f x | None  -> y
let string_of_fsdoco:
  (Prims.string* (Prims.string* Prims.string) Prims.list) Prims.option ->
    Prims.string
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____141 =
           let uu____142 = FStar_Parser_AST.string_of_fsdoc x in
           Prims.strcat uu____142 "*)" in
         Prims.strcat "(*" uu____141) "" d
let string_of_termo: FStar_Parser_AST.term Prims.option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t
let code_wrap: Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")
let string_of_tycon: FStar_Parser_AST.tycon -> Prims.string =
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
                     (fun uu____205  ->
                        match uu____205 with
                        | (id1,t,doco) ->
                            let uu____230 = string_of_fsdoco doco in
                            let uu____231 =
                              let uu____232 =
                                let uu____233 =
                                  FStar_Parser_AST.term_to_string t in
                                Prims.strcat ":" uu____233 in
                              Prims.strcat id1.FStar_Ident.idText uu____232 in
                            Prims.strcat uu____230 uu____231)) in
              FStar_All.pipe_right uu____188 (FStar_String.concat "; ") in
            Prims.strcat uu____187 " }" in
          Prims.strcat " = { " uu____186 in
        Prims.strcat id.FStar_Ident.idText uu____185
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____257 =
          let uu____258 =
            let uu____259 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____280  ->
                      match uu____280 with
                      | (id1,trmo,doco,u) ->
                          let uu____310 = string_of_fsdoco doco in
                          let uu____311 =
                            let uu____312 =
                              let uu____313 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo in
                              Prims.strcat ":" uu____313 in
                            Prims.strcat id1.FStar_Ident.idText uu____312 in
                          Prims.strcat uu____310 uu____311)) in
            FStar_All.pipe_right uu____259 (FStar_String.concat " | ") in
          Prims.strcat " = " uu____258 in
        Prims.strcat id.FStar_Ident.idText uu____257
let string_of_decl': FStar_Parser_AST.decl' -> Prims.string =
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
                   let uu____346 = FStar_Parser_AST.pat_to_string p in
                   let uu____347 = FStar_Parser_AST.term_to_string t in
                   (uu____346, uu____347)) pats in
        let termty' =
          FStar_List.map
            (fun uu____352  ->
               match uu____352 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____357 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____360 =
          let uu____361 =
            let uu____362 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____362 in
          Prims.strcat i.FStar_Ident.idText uu____361 in
        Prims.strcat "assume " uu____360
    | FStar_Parser_AST.Tycon (uu____363,tys) ->
        let uu____373 =
          let uu____374 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____389  ->
                    match uu____389 with
                    | (t,d1) ->
                        let uu____412 = string_of_tycon t in
                        let uu____413 =
                          let uu____414 = string_of_fsdoco d1 in
                          Prims.strcat " " uu____414 in
                        Prims.strcat uu____412 uu____413)) in
          FStar_All.pipe_right uu____374 (FStar_String.concat " and ") in
        Prims.strcat "type " uu____373
    | FStar_Parser_AST.Val (i,t) ->
        let uu____418 =
          let uu____419 =
            let uu____420 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____420 in
          Prims.strcat i.FStar_Ident.idText uu____419 in
        Prims.strcat "val " uu____418
    | FStar_Parser_AST.Exception (i,uu____422) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i,_,_,_))
      |FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i,_,_))
        -> Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____434 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____435 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____437) -> comm
let decl_documented: FStar_Parser_AST.decl -> Prims.bool =
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
              (fun uu____525  ->
                 match uu____525 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars in
      FStar_List.existsb
        (fun uu____543  ->
           match uu____543 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt in
    match d.FStar_Parser_AST.doc with
    | Some uu____551 -> true
    | uu____552 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____554 -> true
         | FStar_Parser_AST.Tycon (uu____555,ty) -> tycon_documented ty
         | uu____565 -> false)
let document_decl:
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____577 = d in
        match uu____577 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____579;
            FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____581;
            FStar_Parser_AST.attrs = uu____582;_} ->
            ((let uu____585 =
                let uu____586 = string_of_decl' d.FStar_Parser_AST.d in
                code_wrap uu____586 in
              w uu____585);
             (match fsdoc with
              | Some (doc1,_kw) -> w (Prims.strcat "\n" doc1)
              | uu____601 -> ());
             w "")
      else ()
let document_toplevel name topdecl =
  match topdecl.FStar_Parser_AST.d with
  | FStar_Parser_AST.TopLevelModule uu____620 ->
      (match topdecl.FStar_Parser_AST.doc with
       | Some (doc1,kw) ->
           let uu____638 =
             FStar_List.tryFind
               (fun uu____644  ->
                  match uu____644 with | (k,v1) -> k = "summary") kw in
           (match uu____638 with
            | None  -> (None, (Some doc1))
            | Some (uu____657,summary) -> ((Some summary), (Some doc1)))
       | None  -> (None, None))
  | uu____665 -> Prims.raise (FStar_Errors.Err "Not a TopLevelModule")
let document_module: FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____673 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____689) -> (n1, d, "interface") in
    match uu____673 with
    | (name,decls,_mt) ->
        let uu____698 = one_toplevel decls in
        (match uu____698 with
         | Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md") in
             let fd = FStar_Util.open_file_for_writing on in
             let w = FStar_Util.append_to_file fd in
             let no_summary = "fsdoc: no-summary-found" in
             let no_comment = "fsdoc: no-comment-found" in
             let uu____717 = document_toplevel name top_decl in
             (match uu____717 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with | Some s -> s | None  -> no_summary in
                  let comment1 =
                    match comment with | Some s -> s | None  -> no_comment in
                  ((let uu____733 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str] in
                    w uu____733);
                   (let uu____735 = FStar_Util.format "%s\n" [summary1] in
                    w uu____735);
                   (let uu____737 = FStar_Util.format "%s\n" [comment1] in
                    w uu____737);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | None  ->
             let uu____743 =
               let uu____744 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str in
               FStar_Errors.Err uu____744 in
             Prims.raise uu____743)
let generate: Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.collect
        (fun fn  ->
           let uu____753 = FStar_Parser_Driver.parse_file fn in
           Prims.fst uu____753) files in
    let mods = FStar_List.map document_module modules in
    let on = FStar_Options.prepend_output_dir "index.md" in
    let fd = FStar_Util.open_file_for_writing on in
    FStar_List.iter
      (fun m  ->
         let uu____768 = FStar_Util.format "%s\n" [m.FStar_Ident.str] in
         FStar_Util.append_to_file fd uu____768) mods;
    FStar_Util.close_file fd