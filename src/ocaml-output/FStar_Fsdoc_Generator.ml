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
                        | (id,t,doco) ->
                            let uu____230 = string_of_fsdoco doco in
                            let uu____231 =
                              let uu____232 =
                                let uu____233 =
                                  FStar_Parser_AST.term_to_string t in
                                Prims.strcat ":" uu____233 in
                              Prims.strcat id.FStar_Ident.idText uu____232 in
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
                      | (id,trmo,doco,u) ->
                          let uu____310 = string_of_fsdoco doco in
                          let uu____311 =
                            let uu____312 =
                              let uu____313 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo in
                              Prims.strcat ":" uu____313 in
                            Prims.strcat id.FStar_Ident.idText uu____312 in
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
                    | (t,d) ->
                        let uu____412 = string_of_tycon t in
                        let uu____413 =
                          let uu____414 = string_of_fsdoco d in
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
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i,_,_,_,_))
      |FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i,_,_))
        -> Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect
      (i,_,_,_,_))|FStar_Parser_AST.NewEffectForFree
      (FStar_Parser_AST.RedefineEffect (i,_,_)) ->
        Prims.strcat "new_effect_for_free " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____447 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____448 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____450) -> comm
let decl_documented: FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract _|FStar_Parser_AST.TyconAbbrev _ ->
            false
        | FStar_Parser_AST.TyconRecord (uu____478,uu____479,uu____480,fields)
            ->
            FStar_List.existsb
              (fun uu____500  ->
                 match uu____500 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____510,uu____511,uu____512,vars)
            ->
            FStar_List.existsb
              (fun uu____538  ->
                 match uu____538 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars in
      FStar_List.existsb
        (fun uu____556  ->
           match uu____556 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt in
    match d.FStar_Parser_AST.doc with
    | Some uu____564 -> true
    | uu____565 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____567 -> true
         | FStar_Parser_AST.Tycon (uu____568,ty) -> tycon_documented ty
         | uu____578 -> false)
let document_decl:
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____590 = d in
        match uu____590 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____592;
            FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____594;
            FStar_Parser_AST.attrs = uu____595;_} ->
            ((let uu____598 =
                let uu____599 = string_of_decl' d.FStar_Parser_AST.d in
                code_wrap uu____599 in
              w uu____598);
             (match fsdoc with
              | Some (doc,_kw) -> w (Prims.strcat "\n" doc)
              | uu____614 -> ());
             w "")
      else ()
let document_toplevel name topdecl =
  match topdecl.FStar_Parser_AST.d with
  | FStar_Parser_AST.TopLevelModule uu____633 ->
      (match topdecl.FStar_Parser_AST.doc with
       | Some (doc,kw) ->
           let uu____651 =
             FStar_List.tryFind
               (fun uu____657  ->
                  match uu____657 with | (k,v) -> k = "summary") kw in
           (match uu____651 with
            | None  -> (None, (Some doc))
            | Some (uu____670,summary) -> ((Some summary), (Some doc)))
       | None  -> (None, None))
  | uu____678 -> Prims.raise (FStar_Errors.Err "Not a TopLevelModule")
let document_module: FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____686 =
      match m with
      | FStar_Parser_AST.Module (n,d) -> (n, d, "module")
      | FStar_Parser_AST.Interface (n,d,uu____702) -> (n, d, "interface") in
    match uu____686 with
    | (name,decls,_mt) ->
        let uu____711 = one_toplevel decls in
        (match uu____711 with
         | Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md") in
             let fd = FStar_Util.open_file_for_writing on in
             let w = FStar_Util.append_to_file fd in
             let no_summary = "fsdoc: no-summary-found" in
             let no_comment = "fsdoc: no-comment-found" in
             let uu____730 = document_toplevel name top_decl in
             (match uu____730 with
              | (summary,comment) ->
                  let summary =
                    match summary with | Some s -> s | None  -> no_summary in
                  let comment =
                    match comment with | Some s -> s | None  -> no_comment in
                  ((let uu____746 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str] in
                    w uu____746);
                   (let uu____748 = FStar_Util.format "%s\n" [summary] in
                    w uu____748);
                   (let uu____750 = FStar_Util.format "%s\n" [comment] in
                    w uu____750);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | None  ->
             let uu____756 =
               let uu____757 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str in
               FStar_Errors.Err uu____757 in
             Prims.raise uu____756)
let generate: Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.collect
        (fun fn  ->
           let uu____766 = FStar_Parser_Driver.parse_file fn in
           Prims.fst uu____766) files in
    let mods = FStar_List.map document_module modules in
    let on = FStar_Options.prepend_output_dir "index.md" in
    let fd = FStar_Util.open_file_for_writing on in
    FStar_List.iter
      (fun m  ->
         let uu____781 = FStar_Util.format "%s\n" [m.FStar_Ident.str] in
         FStar_Util.append_to_file fd uu____781) mods;
    FStar_Util.close_file fd