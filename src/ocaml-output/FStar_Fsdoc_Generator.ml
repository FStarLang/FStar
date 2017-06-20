open Prims
let one_toplevel:
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl* FStar_Parser_AST.decl Prims.list) option
  =
  fun decls  ->
    let uu____10 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____18 -> true
           | uu____19 -> false) decls in
    match uu____10 with
    | (top,nontops) ->
        (match top with | t::[] -> Some (t, nontops) | uu____39 -> None)
type mforest =
  | Leaf of (Prims.string* Prims.string)
  | Branch of mforest FStar_Util.smap
let uu___is_Leaf: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____61 -> false
let __proj__Leaf__item___0: mforest -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | Leaf _0 -> _0
let uu___is_Branch: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____80 -> false
let __proj__Branch__item___0: mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0
let htree: mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50")
let string_of_optiont f y xo = match xo with | Some x -> f x | None  -> y
let string_of_fsdoco:
  (Prims.string* (Prims.string* Prims.string) Prims.list) option ->
    Prims.string
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____147 =
           let uu____148 = FStar_Parser_AST.string_of_fsdoc x in
           Prims.strcat uu____148 "*)" in
         Prims.strcat "(*" uu____147) "" d
let string_of_termo: FStar_Parser_AST.term option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t
let code_wrap: Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")
let string_of_tycon: FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____160 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____166 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id,_bb,_ko,fields) ->
        let uu____191 =
          let uu____192 =
            let uu____193 =
              let uu____194 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____217  ->
                        match uu____217 with
                        | (id1,t,doco) ->
                            let uu____242 = string_of_fsdoco doco in
                            let uu____243 =
                              let uu____244 =
                                let uu____245 =
                                  FStar_Parser_AST.term_to_string t in
                                Prims.strcat ":" uu____245 in
                              Prims.strcat id1.FStar_Ident.idText uu____244 in
                            Prims.strcat uu____242 uu____243)) in
              FStar_All.pipe_right uu____194 (FStar_String.concat "; ") in
            Prims.strcat uu____193 " }" in
          Prims.strcat " = { " uu____192 in
        Prims.strcat id.FStar_Ident.idText uu____191
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____269 =
          let uu____270 =
            let uu____271 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____299  ->
                      match uu____299 with
                      | (id1,trmo,doco,u) ->
                          let uu____329 = string_of_fsdoco doco in
                          let uu____330 =
                            let uu____331 =
                              let uu____332 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo in
                              Prims.strcat ":" uu____332 in
                            Prims.strcat id1.FStar_Ident.idText uu____331 in
                          Prims.strcat uu____329 uu____330)) in
            FStar_All.pipe_right uu____271 (FStar_String.concat " | ") in
          Prims.strcat " = " uu____270 in
        Prims.strcat id.FStar_Ident.idText uu____269
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
    | FStar_Parser_AST.TopLevelLet (uu____342,pats) ->
        let termty =
          FStar_List.map
            (fun uu____363  ->
               match uu____363 with
               | (p,t) ->
                   let uu____370 = FStar_Parser_AST.pat_to_string p in
                   let uu____371 = FStar_Parser_AST.term_to_string t in
                   (uu____370, uu____371)) pats in
        let termty' =
          FStar_List.map
            (fun uu____379  ->
               match uu____379 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____384 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____387 =
          let uu____388 =
            let uu____389 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____389 in
          Prims.strcat i.FStar_Ident.idText uu____388 in
        Prims.strcat "assume " uu____387
    | FStar_Parser_AST.Tycon (uu____390,tys) ->
        let uu____400 =
          let uu____401 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____421  ->
                    match uu____421 with
                    | (t,d1) ->
                        let uu____444 = string_of_tycon t in
                        let uu____445 =
                          let uu____446 = string_of_fsdoco d1 in
                          Prims.strcat " " uu____446 in
                        Prims.strcat uu____444 uu____445)) in
          FStar_All.pipe_right uu____401 (FStar_String.concat " and ") in
        Prims.strcat "type " uu____400
    | FStar_Parser_AST.Val (i,t) ->
        let uu____450 =
          let uu____451 =
            let uu____452 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____452 in
          Prims.strcat i.FStar_Ident.idText uu____451 in
        Prims.strcat "val " uu____450
    | FStar_Parser_AST.Exception (i,uu____454) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____458,uu____459,uu____460)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____466,uu____467)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____470 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____471 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____473) -> comm
let decl_documented: FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____499 -> false
        | FStar_Parser_AST.TyconAbbrev uu____505 -> false
        | FStar_Parser_AST.TyconRecord (uu____512,uu____513,uu____514,fields)
            ->
            FStar_List.existsb
              (fun uu____538  ->
                 match uu____538 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____548,uu____549,uu____550,vars)
            ->
            FStar_List.existsb
              (fun uu____581  ->
                 match uu____581 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars in
      FStar_List.existsb
        (fun uu____602  ->
           match uu____602 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt in
    match d.FStar_Parser_AST.doc with
    | Some uu____610 -> true
    | uu____611 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____613 -> true
         | FStar_Parser_AST.Tycon (uu____614,ty) -> tycon_documented ty
         | uu____624 -> false)
let document_decl:
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____636 = d in
        match uu____636 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____638;
            FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____640;
            FStar_Parser_AST.attrs = uu____641;_} ->
            ((let uu____644 =
                let uu____645 = string_of_decl' d.FStar_Parser_AST.d in
                code_wrap uu____645 in
              w uu____644);
             (match fsdoc with
              | Some (doc1,_kw) -> w (Prims.strcat "\n" doc1)
              | uu____660 -> ());
             w "")
      else ()
let document_toplevel name topdecl =
  match topdecl.FStar_Parser_AST.d with
  | FStar_Parser_AST.TopLevelModule uu____679 ->
      (match topdecl.FStar_Parser_AST.doc with
       | Some (doc1,kw) ->
           let uu____697 =
             FStar_List.tryFind
               (fun uu____706  ->
                  match uu____706 with | (k,v1) -> k = "summary") kw in
           (match uu____697 with
            | None  -> (None, (Some doc1))
            | Some (uu____719,summary) -> ((Some summary), (Some doc1)))
       | None  -> (None, None))
  | uu____727 -> raise (FStar_Errors.Err "Not a TopLevelModule")
let document_module: FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____735 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____751) -> (n1, d, "interface") in
    match uu____735 with
    | (name,decls,_mt) ->
        let uu____760 = one_toplevel decls in
        (match uu____760 with
         | Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md") in
             let fd = FStar_Util.open_file_for_writing on in
             let w = FStar_Util.append_to_file fd in
             let no_summary = "fsdoc: no-summary-found" in
             let no_comment = "fsdoc: no-comment-found" in
             let uu____779 = document_toplevel name top_decl in
             (match uu____779 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with | Some s -> s | None  -> no_summary in
                  let comment1 =
                    match comment with | Some s -> s | None  -> no_comment in
                  ((let uu____795 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str] in
                    w uu____795);
                   (let uu____797 = FStar_Util.format "%s\n" [summary1] in
                    w uu____797);
                   (let uu____799 = FStar_Util.format "%s\n" [comment1] in
                    w uu____799);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | None  ->
             let uu____805 =
               let uu____806 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str in
               FStar_Errors.Err uu____806 in
             raise uu____805)
let generate: Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.collect
        (fun fn  ->
           let uu____817 = FStar_Parser_Driver.parse_file fn in fst uu____817)
        files in
    let mods = FStar_List.map document_module modules in
    let on = FStar_Options.prepend_output_dir "index.md" in
    let fd = FStar_Util.open_file_for_writing on in
    FStar_List.iter
      (fun m  ->
         let uu____834 = FStar_Util.format "%s\n" [m.FStar_Ident.str] in
         FStar_Util.append_to_file fd uu____834) mods;
    FStar_Util.close_file fd