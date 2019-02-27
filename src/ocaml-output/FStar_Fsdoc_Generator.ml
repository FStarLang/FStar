open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____53541 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____53554 -> true
           | uu____53556 -> false) decls
       in
    match uu____53541 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____53593 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____53636 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____53676 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____53707 'Auu____53708 .
    ('Auu____53707 -> 'Auu____53708) ->
      'Auu____53708 ->
        'Auu____53707 FStar_Pervasives_Native.option -> 'Auu____53708
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
         let uu____53801 =
           let uu____53803 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____53803 "*)"  in
         Prims.op_Hat "(*" uu____53801) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____53840 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____53852 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____53898 =
          let uu____53900 =
            let uu____53902 =
              let uu____53904 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____53962  ->
                        match uu____53962 with
                        | (id2,t,doco) ->
                            let uu____54018 = string_of_fsdoco doco  in
                            let uu____54020 =
                              let uu____54022 =
                                let uu____54024 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____54024  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____54022
                               in
                            Prims.op_Hat uu____54018 uu____54020))
                 in
              FStar_All.pipe_right uu____53904 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____53902 " }"  in
          Prims.op_Hat " = { " uu____53900  in
        Prims.op_Hat id1.FStar_Ident.idText uu____53898
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____54076 =
          let uu____54078 =
            let uu____54080 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____54149  ->
                      match uu____54149 with
                      | (id2,trmo,doco,u) ->
                          let uu____54217 = string_of_fsdoco doco  in
                          let uu____54219 =
                            let uu____54221 =
                              let uu____54223 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____54223  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____54221
                             in
                          Prims.op_Hat uu____54217 uu____54219))
               in
            FStar_All.pipe_right uu____54080 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____54078  in
        Prims.op_Hat id1.FStar_Ident.idText uu____54076
  
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
    | FStar_Parser_AST.TopLevelLet (uu____54254,pats) ->
        let termty =
          FStar_List.map
            (fun uu____54292  ->
               match uu____54292 with
               | (p,t) ->
                   let uu____54305 = FStar_Parser_AST.pat_to_string p  in
                   let uu____54307 = FStar_Parser_AST.term_to_string t  in
                   (uu____54305, uu____54307)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____54325  ->
               match uu____54325 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____54342 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____54346 =
          let uu____54348 =
            let uu____54350 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54350  in
          Prims.op_Hat i.FStar_Ident.idText uu____54348  in
        Prims.op_Hat "assume " uu____54346
    | FStar_Parser_AST.Tycon (uu____54354,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____54385 =
          let uu____54387 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____54440  ->
                    match uu____54440 with
                    | (t,d1) ->
                        let uu____54493 = string_of_tycon t  in
                        let uu____54495 =
                          let uu____54497 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____54497  in
                        Prims.op_Hat uu____54493 uu____54495))
             in
          FStar_All.pipe_right uu____54387 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____54385
    | FStar_Parser_AST.Val (i,t) ->
        let uu____54507 =
          let uu____54509 =
            let uu____54511 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____54511  in
          Prims.op_Hat i.FStar_Ident.idText uu____54509  in
        Prims.op_Hat "val " uu____54507
    | FStar_Parser_AST.Exception (i,uu____54516) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____54523,uu____54524,uu____54525)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____54536,uu____54537)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____54543 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____54545 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____54553 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____54553
    | FStar_Parser_AST.Fsdoc (comm,uu____54557) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____54614 -> false
        | FStar_Parser_AST.TyconAbbrev uu____54626 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____54640,uu____54641,uu____54642,fields) ->
            FStar_List.existsb
              (fun uu____54684  ->
                 match uu____54684 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____54701,uu____54702,uu____54703,vars) ->
            FStar_List.existsb
              (fun uu____54761  ->
                 match uu____54761 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____54799  ->
           match uu____54799 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____54814 -> true
    | uu____54816 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____54820 -> true
         | FStar_Parser_AST.Tycon (uu____54822,uu____54823,ty) ->
             tycon_documented ty
         | uu____54845 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____54866 = d  in
        match uu____54866 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____54868;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____54870;
            FStar_Parser_AST.attrs = uu____54871;_} ->
            ((let uu____54875 =
                let uu____54877 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____54877  in
              w uu____54875);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____54901 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____54914 .
    'Auu____54914 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____54935 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____54966 =
                 FStar_List.tryFind
                   (fun uu____54984  ->
                      match uu____54984 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____54966 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____55024,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____55052 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____55071 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____55102) -> (n1, d, "interface")
       in
    match uu____55071 with
    | (name,decls,_mt) ->
        let uu____55122 = one_toplevel decls  in
        (match uu____55122 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____55159 = document_toplevel name top_decl  in
             (match uu____55159 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____55199 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____55199);
                   (let uu____55205 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____55205);
                   (let uu____55211 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____55211);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____55224 =
               let uu____55230 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____55230)  in
             FStar_Errors.raise_err uu____55224)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____55254 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____55254) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____55284 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____55284) mods;
    FStar_Util.close_file fd
  