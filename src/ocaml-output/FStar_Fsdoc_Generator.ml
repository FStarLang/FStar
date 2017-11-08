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
           | FStar_Parser_AST.TopLevelModule uu____28 -> true
           | uu____29 -> false) decls in
    match uu____16 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____65 -> FStar_Pervasives_Native.None)
type mforest =
  | Leaf of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  | Branch of mforest FStar_Util.smap[@@deriving show]
let uu___is_Leaf: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____96 -> false
let __proj__Leaf__item___0:
  mforest -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Leaf _0 -> _0
let uu___is_Branch: mforest -> Prims.bool =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____122 -> false
let __proj__Branch__item___0: mforest -> mforest FStar_Util.smap =
  fun projectee  -> match projectee with | Branch _0 -> _0
let htree: mforest FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50")
let string_of_optiont:
  'Auu____143 'Auu____144 .
    ('Auu____144 -> 'Auu____143) ->
      'Auu____143 ->
        'Auu____144 FStar_Pervasives_Native.option -> 'Auu____143
  =
  fun f  ->
    fun y  ->
      fun xo  ->
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
         let uu____217 =
           let uu____218 = FStar_Parser_AST.string_of_fsdoc x in
           Prims.strcat uu____218 "*)" in
         Prims.strcat "(*" uu____217) "" d
let string_of_termo:
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t
let code_wrap: Prims.string -> Prims.string =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")
let string_of_tycon: FStar_Parser_AST.tycon -> Prims.string =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____232 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____243 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id,_bb,_ko,fields) ->
        let uu____288 =
          let uu____289 =
            let uu____290 =
              let uu____291 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____330  ->
                        match uu____330 with
                        | (id1,t,doco) ->
                            let uu____376 = string_of_fsdoco doco in
                            let uu____377 =
                              let uu____378 =
                                let uu____379 =
                                  FStar_Parser_AST.term_to_string t in
                                Prims.strcat ":" uu____379 in
                              Prims.strcat id1.FStar_Ident.idText uu____378 in
                            Prims.strcat uu____376 uu____377)) in
              FStar_All.pipe_right uu____291 (FStar_String.concat "; ") in
            Prims.strcat uu____290 " }" in
          Prims.strcat " = { " uu____289 in
        Prims.strcat id.FStar_Ident.idText uu____288
    | FStar_Parser_AST.TyconVariant (id,_bb,_ko,vars) ->
        let uu____422 =
          let uu____423 =
            let uu____424 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____472  ->
                      match uu____472 with
                      | (id1,trmo,doco,u) ->
                          let uu____527 = string_of_fsdoco doco in
                          let uu____528 =
                            let uu____529 =
                              let uu____530 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo in
                              Prims.strcat ":" uu____530 in
                            Prims.strcat id1.FStar_Ident.idText uu____529 in
                          Prims.strcat uu____527 uu____528)) in
            FStar_All.pipe_right uu____424 (FStar_String.concat " | ") in
          Prims.strcat " = " uu____423 in
        Prims.strcat id.FStar_Ident.idText uu____422
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
    | FStar_Parser_AST.TopLevelLet (uu____541,pats) ->
        let termty =
          FStar_List.map
            (fun uu____575  ->
               match uu____575 with
               | (p,t) ->
                   let uu____586 = FStar_Parser_AST.pat_to_string p in
                   let uu____587 = FStar_Parser_AST.term_to_string t in
                   (uu____586, uu____587)) pats in
        let termty' =
          FStar_List.map
            (fun uu____598  ->
               match uu____598 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____605 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____608 =
          let uu____609 =
            let uu____610 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____610 in
          Prims.strcat i.FStar_Ident.idText uu____609 in
        Prims.strcat "assume " uu____608
    | FStar_Parser_AST.Tycon (uu____611,tys) ->
        let uu____629 =
          let uu____630 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____664  ->
                    match uu____664 with
                    | (t,d1) ->
                        let uu____707 = string_of_tycon t in
                        let uu____708 =
                          let uu____709 = string_of_fsdoco d1 in
                          Prims.strcat " " uu____709 in
                        Prims.strcat uu____707 uu____708)) in
          FStar_All.pipe_right uu____630 (FStar_String.concat " and ") in
        Prims.strcat "type " uu____629
    | FStar_Parser_AST.Val (i,t) ->
        let uu____714 =
          let uu____715 =
            let uu____716 = FStar_Parser_AST.term_to_string t in
            Prims.strcat ":" uu____716 in
          Prims.strcat i.FStar_Ident.idText uu____715 in
        Prims.strcat "val " uu____714
    | FStar_Parser_AST.Exception (i,uu____718) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____724,uu____725,uu____726)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____736,uu____737)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____742 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____743 -> "pragma"
    | FStar_Parser_AST.Fsdoc (comm,uu____745) -> comm
let decl_documented: FStar_Parser_AST.decl -> Prims.bool =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____785 -> false
        | FStar_Parser_AST.TyconAbbrev uu____796 -> false
        | FStar_Parser_AST.TyconRecord (uu____809,uu____810,uu____811,fields)
            ->
            FStar_List.existsb
              (fun uu____853  ->
                 match uu____853 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____869,uu____870,uu____871,vars)
            ->
            FStar_List.existsb
              (fun uu____926  ->
                 match uu____926 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars in
      FStar_List.existsb
        (fun uu____960  ->
           match uu____960 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____973 -> true
    | uu____974 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____977 -> true
         | FStar_Parser_AST.Tycon (uu____978,ty) -> tycon_documented ty
         | uu____996 -> false)
let document_decl:
  (Prims.string -> Prims.unit) -> FStar_Parser_AST.decl -> Prims.unit =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1008 = d in
        match uu____1008 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1010;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1012;
            FStar_Parser_AST.attrs = uu____1013;_} ->
            ((let uu____1017 =
                let uu____1018 = string_of_decl' d.FStar_Parser_AST.d in
                code_wrap uu____1018 in
              w uu____1017);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1044 -> ());
             w "")
      else ()
let document_toplevel:
  'Auu____1051 .
    'Auu____1051 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1068 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____1101 =
                 FStar_List.tryFind
                   (fun uu____1115  ->
                      match uu____1115 with | (k,v1) -> k = "summary") kw in
               (match uu____1101 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1138,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1152 ->
          FStar_Exn.raise (FStar_Errors.Err "Not a TopLevelModule")
let document_module: FStar_Parser_AST.modul -> FStar_Ident.lid =
  fun m  ->
    let uu____1164 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1191) -> (n1, d, "interface") in
    match uu____1164 with
    | (name,decls,_mt) ->
        let uu____1205 = one_toplevel decls in
        (match uu____1205 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md") in
             let fd = FStar_Util.open_file_for_writing on in
             let w = FStar_Util.append_to_file fd in
             let no_summary = "fsdoc: no-summary-found" in
             let no_comment = "fsdoc: no-comment-found" in
             let uu____1233 = document_toplevel name top_decl in
             (match uu____1233 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment in
                  ((let uu____1257 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str] in
                    w uu____1257);
                   (let uu____1259 = FStar_Util.format "%s\n" [summary1] in
                    w uu____1259);
                   (let uu____1261 = FStar_Util.format "%s\n" [comment1] in
                    w uu____1261);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____1270 =
               let uu____1271 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str in
               FStar_Errors.Err uu____1271 in
             FStar_Exn.raise uu____1270)
let generate: Prims.string Prims.list -> Prims.unit =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____1285 = FStar_Parser_Driver.parse_file fn in
           FStar_Pervasives_Native.fst uu____1285) files in
    let mods = FStar_List.map document_module modules in
    let on = FStar_Options.prepend_output_dir "index.md" in
    let fd = FStar_Util.open_file_for_writing on in
    FStar_List.iter
      (fun m  ->
         let uu____1311 = FStar_Util.format "%s\n" [m.FStar_Ident.str] in
         FStar_Util.append_to_file fd uu____1311) mods;
    FStar_Util.close_file fd