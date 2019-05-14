open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____37 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____70 -> true
           | uu____76 -> false) decls
       in
    match uu____37 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____188 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string * Prims.string) 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____246 -> false
  
let (__proj__Leaf__item___0 : mforest -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____285 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____315 'Auu____316 .
    ('Auu____315 -> 'Auu____316) ->
      'Auu____316 ->
        'Auu____315 FStar_Pervasives_Native.option -> 'Auu____316
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
         let uu____409 =
           let uu____411 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.op_Hat uu____411 "*)"  in
         Prims.op_Hat "(*" uu____409) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____457 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____478 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____564 =
          let uu____566 =
            let uu____568 =
              let uu____570 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____638  ->
                        match uu____638 with
                        | (id2,t,doco) ->
                            let uu____709 = string_of_fsdoco doco  in
                            let uu____711 =
                              let uu____713 =
                                let uu____715 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.op_Hat ":" uu____715  in
                              Prims.op_Hat id2.FStar_Ident.idText uu____713
                               in
                            Prims.op_Hat uu____709 uu____711))
                 in
              FStar_All.pipe_right uu____570 (FStar_String.concat "; ")  in
            Prims.op_Hat uu____568 " }"  in
          Prims.op_Hat " = { " uu____566  in
        Prims.op_Hat id1.FStar_Ident.idText uu____564
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____795 =
          let uu____797 =
            let uu____799 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____878  ->
                      match uu____878 with
                      | (id2,trmo,doco,u) ->
                          let uu____961 = string_of_fsdoco doco  in
                          let uu____963 =
                            let uu____965 =
                              let uu____967 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.op_Hat ":" uu____967  in
                            Prims.op_Hat id2.FStar_Ident.idText uu____965  in
                          Prims.op_Hat uu____961 uu____963))
               in
            FStar_All.pipe_right uu____799 (FStar_String.concat " | ")  in
          Prims.op_Hat " = " uu____797  in
        Prims.op_Hat id1.FStar_Ident.idText uu____795
  
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
    | FStar_Parser_AST.TopLevelLet (uu____1029,pats) ->
        let termty =
          FStar_List.map
            (fun uu____1082  ->
               match uu____1082 with
               | (p,t) ->
                   let uu____1110 = FStar_Parser_AST.pat_to_string p  in
                   let uu____1112 = FStar_Parser_AST.term_to_string t  in
                   (uu____1110, uu____1112)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____1130  ->
               match uu____1130 with
               | (p,t) -> Prims.op_Hat p (Prims.op_Hat ":" t)) termty
           in
        Prims.op_Hat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____1147 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____1164 =
          let uu____1166 =
            let uu____1168 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____1168  in
          Prims.op_Hat i.FStar_Ident.idText uu____1166  in
        Prims.op_Hat "assume " uu____1164
    | FStar_Parser_AST.Tycon (uu____1172,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____1203 =
          let uu____1205 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____1258  ->
                    match uu____1258 with
                    | (t,d1) ->
                        let uu____1311 = string_of_tycon t  in
                        let uu____1313 =
                          let uu____1315 = string_of_fsdoco d1  in
                          Prims.op_Hat " " uu____1315  in
                        Prims.op_Hat uu____1311 uu____1313))
             in
          FStar_All.pipe_right uu____1205 (FStar_String.concat " and ")  in
        Prims.op_Hat s uu____1203
    | FStar_Parser_AST.Val (i,t) ->
        let uu____1335 =
          let uu____1337 =
            let uu____1339 = FStar_Parser_AST.term_to_string t  in
            Prims.op_Hat ":" uu____1339  in
          Prims.op_Hat i.FStar_Ident.idText uu____1337  in
        Prims.op_Hat "val " uu____1335
    | FStar_Parser_AST.Exception (i,uu____1344) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____1361,uu____1362,uu____1363)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____1402,uu____1403)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____1427 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____1436 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____1454 = FStar_Parser_AST.term_to_string t  in
        Prims.op_Hat "splice " uu____1454
    | FStar_Parser_AST.Fsdoc (comm,uu____1458) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____1525 -> false
        | FStar_Parser_AST.TyconAbbrev uu____1546 -> false
        | FStar_Parser_AST.TyconRecord
            (uu____1572,uu____1573,uu____1574,fields) ->
            FStar_List.existsb
              (fun uu____1649  ->
                 match uu____1649 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant
            (uu____1681,uu____1682,uu____1683,vars) ->
            FStar_List.existsb
              (fun uu____1774  ->
                 match uu____1774 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____1827  ->
           match uu____1827 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____1842 -> true
    | uu____1844 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____1848 -> true
         | FStar_Parser_AST.Tycon (uu____1850,uu____1851,ty) ->
             tycon_documented ty
         | uu____1873 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1904 = d  in
        match uu____1904 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1916;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1918;
            FStar_Parser_AST.attrs = uu____1919;_} ->
            ((let uu____1923 =
                let uu____1925 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____1925  in
              w uu____1923);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.op_Hat "\n" doc1)
              | uu____1949 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____1962 .
    'Auu____1962 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option * Prims.string
          FStar_Pervasives_Native.option)
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1993 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____2028 =
                 FStar_List.tryFind
                   (fun uu____2046  ->
                      match uu____2046 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____2028 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____2086,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____2114 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____2137 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____2213) -> (n1, d, "interface")
       in
    match uu____2137 with
    | (name,decls,_mt) ->
        let uu____2282 = one_toplevel decls  in
        (match uu____2282 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on1 =
               FStar_Options.prepend_output_dir
                 (Prims.op_Hat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on1  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____2363 = document_toplevel name top_decl  in
             (match uu____2363 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____2411 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____2411);
                   (let uu____2417 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____2417);
                   (let uu____2423 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____2423);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____2451 =
               let uu____2457 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____2457)  in
             FStar_Errors.raise_err uu____2451)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____2485 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____2485) files
       in
    let mods = FStar_List.map document_module modules  in
    let on1 = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on1  in
    FStar_List.iter
      (fun m  ->
         let uu____2531 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____2531) mods;
    FStar_Util.close_file fd
  