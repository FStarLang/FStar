open Prims
let one_toplevel:
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun decls  ->
    let uu____16 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____26 -> true
           | uu____27 -> false) decls in
    match uu____16 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____63 -> FStar_Pervasives_Native.None)
type mforest =
  | Leaf of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  | Branch of mforest FStar_Util.smap
let uu___is_Leaf: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____94 -> false
let __proj__Leaf__item___0:
  mforest -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Leaf _0 -> _0
let uu___is_Branch: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____120 -> false
let __proj__Branch__item___0: mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0
let htree: mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50")
let string_of_optiont f y xo =
  match xo with
  | FStar_Pervasives_Native.Some x -> f x
  | FStar_Pervasives_Native.None  -> y
let string_of_fsdoco:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
    Prims.string
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____213 =
           let uu____214 = FStar_Parser_AST.string_of_fsdoc x in
           Prims.strcat uu____214 "*)" in
         Prims.strcat "(*" uu____213) "" d
let string_of_termo:
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t
let code_wrap: Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")
let string_of_tycon: FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____228 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____239 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id,_bb,_ko,fields) ->
        let uu____284 =
          let uu____285 =
            let uu____286 =
              let uu____287 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____320  ->
                        match uu____320 with
                        | (id1,t,doco) ->
                            let uu____366 = string_of_fsdoco doco in
                            let uu____367 =
                              let uu____368 =
                                let uu____369 =
                                  FStar_Parser_AST.term_to_string t in
                                Prims.strcat ":" uu____369 in
                              Prims.strcat id1.FStar_Ident.idText uu____368 in
                            Prims.strcat uu____366 uu____367)) in
              FStar_All.pipe_right uu____287 (FStar_String.concat "; ") in
            Prims.strcat uu____286 " }" in
          Prims.strcat " = { " uu____285 in
        Prims.strcat id.FStar_Ident.idText uu____284
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____412 =
          let uu____413 =
            let uu____414 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____455  ->
                      match uu____455 with
                      | (id1,trmo,doco,u) ->
                          let uu____510 = string_of_fsdoco doco in
                          let uu____511 =
                            let uu____512 =
                              let uu____513 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo in
                              Prims.strcat ":" uu____513 in
                            Prims.strcat id1.FStar_Ident.idText uu____512 in
                          Prims.strcat uu____510 uu____511)) in
            FStar_All.pipe_right uu____414 (FStar_String.concat " | ") in
          Prims.strcat " = " uu____413 in
        Prims.strcat id.FStar_Ident.idText uu____412
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
    | FStar_Parser_AST.TopLevelLet (uu____524,pats) ->
        let termty =
          FStar_List.map
            (fun uu____553  ->
               match uu____553 with
               | (p,t) ->
                   let uu____564 = FStar_Parser_AST.pat_to_string p in
                   let uu____565 = FStar_Parser_AST.term_to_string t in
                   (uu____564, uu____565)) pats in
        let termty' =
          FStar_List.map
            (fun uu____573  ->
               match uu____573 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____580 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____583 =
          let uu____584 =
            let uu____585 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____585 in
          Prims.strcat i.FStar_Ident.idText uu____584 in
        Prims.strcat "assume " uu____583
    | FStar_Parser_AST.Tycon (uu____586,tys) ->
        let uu____604 =
          let uu____605 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____634  ->
                    match uu____634 with
                    | (t,d1) ->
                        let uu____677 = string_of_tycon t in
                        let uu____678 =
                          let uu____679 = string_of_fsdoco d1 in
                          Prims.strcat " " uu____679 in
                        Prims.strcat uu____677 uu____678)) in
          FStar_All.pipe_right uu____605 (FStar_String.concat " and ") in
        Prims.strcat "type " uu____604
    | FStar_Parser_AST.Val (i,t) ->
        let uu____684 =
          let uu____685 =
            let uu____686 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____686 in
          Prims.strcat i.FStar_Ident.idText uu____685 in
        Prims.strcat "val " uu____684
    | FStar_Parser_AST.Exception (i,uu____688) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____694,uu____695,uu____696)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____706,uu____707)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____712 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____713 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____715) -> comm
let decl_documented: FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____755 -> false
        | FStar_Parser_AST.TyconAbbrev uu____766 -> false
        | FStar_Parser_AST.TyconRecord (uu____779,uu____780,uu____781,fields)
            ->
            FStar_List.existsb
              (fun uu____819  ->
                 match uu____819 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____835,uu____836,uu____837,vars)
            ->
            FStar_List.existsb
              (fun uu____887  ->
                 match uu____887 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars in
      FStar_List.existsb
        (fun uu____918  ->
           match uu____918 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____931 -> true
    | uu____932 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____935 -> true
         | FStar_Parser_AST.Tycon (uu____936,ty) -> tycon_documented ty
         | uu____954 -> false)
let document_decl:
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____966 = d in
        match uu____966 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____968;
            FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____970;
            FStar_Parser_AST.attrs = uu____971;_} ->
            ((let uu____975 =
                let uu____976 = string_of_decl' d.FStar_Parser_AST.d in
                code_wrap uu____976 in
              w uu____975);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1002 -> ());
             w "")
      else ()
let document_toplevel name topdecl =
  match topdecl.FStar_Parser_AST.d with
  | FStar_Parser_AST.TopLevelModule uu____1026 ->
      (match topdecl.FStar_Parser_AST.doc with
       | FStar_Pervasives_Native.Some (doc1,kw) ->
           let uu____1059 =
             FStar_List.tryFind
               (fun uu____1070  ->
                  match uu____1070 with | (k,v1) -> k = "summary") kw in
           (match uu____1059 with
            | FStar_Pervasives_Native.None  ->
                (FStar_Pervasives_Native.None,
                  (FStar_Pervasives_Native.Some doc1))
            | FStar_Pervasives_Native.Some (uu____1093,summary) ->
                ((FStar_Pervasives_Native.Some summary),
                  (FStar_Pervasives_Native.Some doc1)))
       | FStar_Pervasives_Native.None  ->
           (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
  | uu____1107 -> raise (FStar_Errors.Err "Not a TopLevelModule")
let document_module: FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____1119 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1146) -> (n1, d, "interface") in
    match uu____1119 with
    | (name,decls,_mt) ->
        let uu____1160 = one_toplevel decls in
        (match uu____1160 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md") in
             let fd = FStar_Util.open_file_for_writing on in
             let w = FStar_Util.append_to_file fd in
             let no_summary = "fsdoc: no-summary-found" in
             let no_comment = "fsdoc: no-comment-found" in
             let uu____1188 = document_toplevel name top_decl in
             (match uu____1188 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment in
                  ((let uu____1212 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str] in
                    w uu____1212);
                   (let uu____1214 = FStar_Util.format "%s\n" [summary1] in
                    w uu____1214);
                   (let uu____1216 = FStar_Util.format "%s\n" [comment1] in
                    w uu____1216);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____1225 =
               let uu____1226 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str in
               FStar_Errors.Err uu____1226 in
             raise uu____1225)
let generate: Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.collect
        (fun fn  ->
           let uu____1238 = FStar_Parser_Driver.parse_file fn in
           FStar_Pervasives_Native.fst uu____1238) files in
    let mods = FStar_List.map document_module modules in
    let on = FStar_Options.prepend_output_dir "index.md" in
    let fd = FStar_Util.open_file_for_writing on in
    FStar_List.iter
      (fun m  ->
         let uu____1262 = FStar_Util.format "%s\n" [m.FStar_Ident.str] in
         FStar_Util.append_to_file fd uu____1262) mods;
    FStar_Util.close_file fd