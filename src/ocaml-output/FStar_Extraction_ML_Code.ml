open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____62634 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____62645 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____62656 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____62667 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____62678 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____62694 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____62705 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____62717 -> false
  
let (__proj__Infix__item___0 : fixity -> assoc) =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int * fixity)
type level = (opprec * assoc)
let (t_prio_fun : (Prims.int * fixity)) =
  ((Prims.parse_int "10"), (Infix Right)) 
let (t_prio_tpl : (Prims.int * fixity)) =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let (t_prio_name : (Prims.int * fixity)) = ((Prims.parse_int "30"), Postfix) 
let (e_bin_prio_lambda : (Prims.int * fixity)) =
  ((Prims.parse_int "5"), Prefix) 
let (e_bin_prio_if : (Prims.int * fixity)) = ((Prims.parse_int "15"), Prefix) 
let (e_bin_prio_letin : (Prims.int * fixity)) =
  ((Prims.parse_int "19"), Prefix) 
let (e_bin_prio_or : (Prims.int * fixity)) =
  ((Prims.parse_int "20"), (Infix Left)) 
let (e_bin_prio_and : (Prims.int * fixity)) =
  ((Prims.parse_int "25"), (Infix Left)) 
let (e_bin_prio_eq : (Prims.int * fixity)) =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let (e_bin_prio_order : (Prims.int * fixity)) =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let (e_bin_prio_op1 : (Prims.int * fixity)) =
  ((Prims.parse_int "30"), (Infix Left)) 
let (e_bin_prio_op2 : (Prims.int * fixity)) =
  ((Prims.parse_int "40"), (Infix Left)) 
let (e_bin_prio_op3 : (Prims.int * fixity)) =
  ((Prims.parse_int "50"), (Infix Left)) 
let (e_bin_prio_op4 : (Prims.int * fixity)) =
  ((Prims.parse_int "60"), (Infix Left)) 
let (e_bin_prio_comb : (Prims.int * fixity)) =
  ((Prims.parse_int "70"), (Infix Left)) 
let (e_bin_prio_seq : (Prims.int * fixity)) =
  ((Prims.parse_int "100"), (Infix Left)) 
let (e_app_prio : (Prims.int * fixity)) =
  ((Prims.parse_int "10000"), (Infix Left)) 
let (min_op_prec : (Prims.int * fixity)) =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let (max_op_prec : (Prims.int * fixity)) =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns : 'a . ('a Prims.list * 'a Prims.list) -> Prims.bool =
  fun x  ->
    match x with
    | ([],uu____62915) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____62939,uu____62940) -> false
  
let (path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list)
  =
  fun currentModule  ->
    fun ns  ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns  in
      if ns' = currentModule
      then []
      else
        (let cg_libs = FStar_Options.codegen_libs ()  in
         let ns_len = FStar_List.length ns  in
         let found =
           FStar_Util.find_map cg_libs
             (fun cg_path  ->
                let cg_len = FStar_List.length cg_path  in
                if (FStar_List.length cg_path) < ns_len
                then
                  let uu____63025 = FStar_Util.first_N cg_len ns  in
                  match uu____63025 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____63069 =
                           let uu____63073 =
                             let uu____63077 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____63077]  in
                           FStar_List.append pfx uu____63073  in
                         FStar_Pervasives_Native.Some uu____63069
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None)
            in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
  
let (mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath)
  =
  fun currentModule  ->
    fun x  ->
      let uu____63123 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____63123 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____63139 ->
          let uu____63141 = x  in
          (match uu____63141 with
           | (ns,x1) ->
               let uu____63152 = path_of_ns currentModule ns  in
               (uu____63152, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____63170 =
      let uu____63172 =
        let uu____63174 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____63174  in
      let uu____63177 = FStar_String.get s (Prims.parse_int "0")  in
      uu____63172 <> uu____63177  in
    if uu____63170 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____63213 = mlpath_of_mlpath currentModule mlp  in
         match uu____63213 with
         | (p,s) ->
             let uu____63225 =
               let uu____63229 =
                 let uu____63233 = ptsym_of_symbol s  in [uu____63233]  in
               FStar_List.append p uu____63229  in
             FStar_String.concat "." uu____63225)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____63254 = mlpath_of_mlpath currentModule mlp  in
      match uu____63254 with
      | (p,s) ->
          let s1 =
            let uu____63268 =
              let uu____63270 =
                let uu____63272 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____63272  in
              let uu____63275 = FStar_String.get s (Prims.parse_int "0")  in
              uu____63270 <> uu____63275  in
            if uu____63268 then Prims.op_Hat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
  
let (infix_prim_ops :
  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list) =
  [("op_Addition", e_bin_prio_op1, "+");
  ("op_Subtraction", e_bin_prio_op1, "-");
  ("op_Multiply", e_bin_prio_op1, "*");
  ("op_Division", e_bin_prio_op1, "/");
  ("op_Equality", e_bin_prio_eq, "=");
  ("op_Colon_Equals", e_bin_prio_eq, ":=");
  ("op_disEquality", e_bin_prio_eq, "<>");
  ("op_AmpAmp", e_bin_prio_and, "&&");
  ("op_BarBar", e_bin_prio_or, "||");
  ("op_LessThanOrEqual", e_bin_prio_order, "<=");
  ("op_GreaterThanOrEqual", e_bin_prio_order, ">=");
  ("op_LessThan", e_bin_prio_order, "<");
  ("op_GreaterThan", e_bin_prio_order, ">");
  ("op_Modulus", e_bin_prio_order, "mod")] 
let (prim_uni_ops : unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____63638  ->
    let op_minus =
      let uu____63641 =
        let uu____63643 = FStar_Options.codegen ()  in
        uu____63643 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____63641 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____63692 . unit -> 'Auu____63692 Prims.list =
  fun uu____63695  -> [] 
let (prim_constructors : (Prims.string * Prims.string) Prims.list) =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let (is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool) =
  fun ns  -> ns = ["Prims"] 
let (as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) *
      Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu____63790  ->
    match uu____63790 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____63849  ->
               match uu____63849 with | (y,uu____63865,uu____63866) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____63904 = as_bin_op p  in
    uu____63904 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____63961  ->
    match uu____63961 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____63989 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____64007  ->
               match uu____64007 with | (y,uu____64016) -> x = y) uu____63989
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64037 = as_uni_op p  in
    uu____64037 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64081  ->
    match uu____64081 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____64118  ->
               match uu____64118 with | (y,uu____64127) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64148 = as_standard_constructor p  in
    uu____64148 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____64198  ->
    fun inner  ->
      fun doc1  ->
        match uu____64198 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____64264 = _inner  in
              match uu____64264 with
              | (pi,fi) ->
                  let uu____64275 = _outer  in
                  (match uu____64275 with
                   | (po,fo) ->
                       (pi > po) ||
                         ((match (fi, side1) with
                           | (Postfix ,Left ) -> true
                           | (Prefix ,Right ) -> true
                           | (Infix (Left ),Left ) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right ),Right ) ->
                               (pi = po) && (fo = (Infix Right))
                           | (Infix (Left ),ILeft ) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right ),IRight ) ->
                               (pi = po) && (fo = (Infix Right))
                           | (uu____64293,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____64295,uu____64296) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___543_64335  ->
      if uu___543_64335 = 92
      then "\\\\"
      else
        if uu___543_64335 = 32
        then " "
        else
          if uu___543_64335 = 8
          then "\\b"
          else
            if uu___543_64335 = 9
            then "\\t"
            else
              if uu___543_64335 = 13
              then "\\r"
              else
                if uu___543_64335 = 10
                then "\\n"
                else
                  if uu___543_64335 = 39
                  then "\\'"
                  else
                    if uu___543_64335 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_64335
                      then FStar_Util.string_of_char uu___543_64335
                      else
                        if FStar_Util.is_punctuation uu___543_64335
                        then FStar_Util.string_of_char uu___543_64335
                        else
                          if FStar_Util.is_symbol uu___543_64335
                          then FStar_Util.string_of_char uu___543_64335
                          else fallback uu___543_64335
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____64382 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____64382
          (if
             ((nc >= (Prims.parse_int "32")) &&
                (nc <= (Prims.parse_int "127")))
               && (nc <> (Prims.parse_int "34"))
           then
             Prims.op_Hat " (*"
               (Prims.op_Hat (FStar_Util.string_of_char c) "*)")
           else "")
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.op_Hat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.op_Hat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64446,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64460,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____64492 =
          let uu____64494 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____64494 "\""  in
        Prims.op_Hat "\"" uu____64492
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____64500 =
          let uu____64502 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____64502 "\""  in
        Prims.op_Hat "\"" uu____64500
    | uu____64506 ->
        failwith "TODO: extract integer constants properly into OCaml"
  
let rec (doc_of_mltype' :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s 95 117
              else s  in
            FStar_Format.text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc2 =
              let uu____64565 =
                let uu____64566 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____64566  in
              FStar_Format.parens uu____64565  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____64576 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____64582 =
                    let uu____64583 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____64583  in
                  FStar_Format.parens uu____64582
               in
            let name1 = ptsym currentModule name  in
            let uu____64587 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____64587
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____64589,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____64593 =
              let uu____64594 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____64594  in
            maybe_paren outer t_prio_fun uu____64593
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____64596 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64596
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> FStar_Format.text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____64608 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____64608

let rec (doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____64701 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64701
            then
              let uu____64704 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____64704
            else
              (let uu____64708 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____64708)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs
               in
            let uu____64722 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____64722
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____64724 = string_of_mlconstant c  in
            FStar_Format.text uu____64724
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____64729 = ptsym currentModule path  in
            FStar_Format.text uu____64729
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____64763 =
              match uu____64763 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____64774 =
                    let uu____64777 =
                      let uu____64778 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____64778  in
                    [uu____64777; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____64774
               in
            let uu____64785 =
              let uu____64786 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____64786  in
            FStar_Format.cbrackets uu____64785
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____64800 = is_standard_constructor ctor  in
              if uu____64800
              then
                let uu____64804 =
                  let uu____64811 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64811  in
                FStar_Pervasives_Native.snd uu____64804
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____64838 = is_standard_constructor ctor  in
              if uu____64838
              then
                let uu____64842 =
                  let uu____64849 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64849  in
                FStar_Pervasives_Native.snd uu____64842
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____64882,uu____64883) ->
                  let uu____64890 =
                    let uu____64893 =
                      let uu____64896 =
                        let uu____64897 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____64897  in
                      [uu____64896]  in
                    (FStar_Format.text name) :: uu____64893  in
                  FStar_Format.reduce1 uu____64890
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____64908 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____64908) es
               in
            let docs1 =
              let uu____64910 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____64910  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____64927 =
                  let uu____64930 =
                    let uu____64933 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____64933]  in
                  FStar_Format.hardline :: uu____64930  in
                FStar_Format.reduce uu____64927
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____64942 =
              let uu____64943 =
                let uu____64946 =
                  let uu____64949 =
                    let uu____64952 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____64952]  in
                  doc1 :: uu____64949  in
                pre :: uu____64946  in
              FStar_Format.combine FStar_Format.hardline uu____64943  in
            FStar_Format.parens uu____64942
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____64963::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____64965;
                    FStar_Extraction_ML_Syntax.loc = uu____64966;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____64968)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____64970;
                  FStar_Extraction_ML_Syntax.loc = uu____64971;_}::[])
                 when
                 let uu____65015 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____65015 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____65041;
                            FStar_Extraction_ML_Syntax.loc = uu____65042;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____65044;
                       FStar_Extraction_ML_Syntax.loc = uu____65045;_} when
                       arg = arg' -> branches
                   | e2 ->
                       [(FStar_Extraction_ML_Syntax.MLP_Wild,
                          FStar_Pervasives_Native.None, e2)]
                    in
                 doc_of_expr currentModule outer
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_Try
                          (scrutinee, branches));
                     FStar_Extraction_ML_Syntax.mlty =
                       (possible_match.FStar_Extraction_ML_Syntax.mlty);
                     FStar_Extraction_ML_Syntax.loc =
                       (possible_match.FStar_Extraction_ML_Syntax.loc)
                   }
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e11::e2::[]) when
                 is_bin_op p -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____65103;
                   FStar_Extraction_ML_Syntax.loc = uu____65104;_},unitVal::[]),e11::e2::[])
                 when
                 (is_bin_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e11::[]) when
                 is_uni_op p -> doc_of_uniop currentModule p e11
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____65117;
                   FStar_Extraction_ML_Syntax.loc = uu____65118;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____65125 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____65136 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____65136)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____65141 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65141
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____65151 =
                   let uu____65154 =
                     let uu____65157 =
                       let uu____65160 =
                         let uu____65161 = ptsym currentModule f  in
                         FStar_Format.text uu____65161  in
                       [uu____65160]  in
                     (FStar_Format.text ".") :: uu____65157  in
                   e2 :: uu____65154  in
                 FStar_Format.reduce uu____65151)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____65197 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65197
              then
                let uu____65200 =
                  let uu____65203 =
                    let uu____65206 =
                      let uu____65209 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____65211 =
                              let uu____65214 =
                                let uu____65217 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____65217]  in
                              (FStar_Format.text " : ") :: uu____65214  in
                            FStar_Format.reduce1 uu____65211
                        | uu____65219 -> FStar_Format.text ""  in
                      [uu____65209; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____65206  in
                  (FStar_Format.text "(") :: uu____65203  in
                FStar_Format.reduce1 uu____65200
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____65238  ->
                   match uu____65238 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____65250 =
                let uu____65253 =
                  let uu____65256 = FStar_Format.reduce1 ids1  in
                  [uu____65256; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____65253  in
              FStar_Format.reduce1 uu____65250  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65265 =
                let uu____65268 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65272 =
                  let uu____65275 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____65275; FStar_Format.text "end"]  in
                uu____65268 :: uu____65272  in
              FStar_Format.combine FStar_Format.hardline uu____65265  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65284 =
                let uu____65287 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65291 =
                  let uu____65294 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____65295 =
                    let uu____65298 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____65302 =
                      let uu____65305 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____65305; FStar_Format.text "end"]  in
                    uu____65298 :: uu____65302  in
                  uu____65294 :: uu____65295  in
                uu____65287 :: uu____65291  in
              FStar_Format.combine FStar_Format.hardline uu____65284  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____65344 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____65344 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____65351 =
              let uu____65354 =
                let uu____65357 =
                  let uu____65358 = ptctor currentModule exn  in
                  FStar_Format.text uu____65358  in
                [uu____65357]  in
              (FStar_Format.text "raise") :: uu____65354  in
            FStar_Format.reduce1 uu____65351
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____65370 =
              let uu____65373 =
                let uu____65376 =
                  let uu____65377 = ptctor currentModule exn  in
                  FStar_Format.text uu____65377  in
                let uu____65379 =
                  let uu____65382 =
                    let uu____65383 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____65383  in
                  [uu____65382]  in
                uu____65376 :: uu____65379  in
              (FStar_Format.text "raise") :: uu____65373  in
            FStar_Format.reduce1 uu____65370
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____65408 =
              let uu____65411 =
                let uu____65414 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____65415 =
                  let uu____65418 =
                    let uu____65421 =
                      let uu____65422 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____65422
                       in
                    [uu____65421]  in
                  (FStar_Format.text "with") :: uu____65418  in
                uu____65414 :: uu____65415  in
              (FStar_Format.text "try") :: uu____65411  in
            FStar_Format.combine FStar_Format.hardline uu____65408
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1

and (doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____65446 =
            let uu____65460 = as_bin_op p  in FStar_Option.get uu____65460
             in
          match uu____65446 with
          | (uu____65489,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21]  in
              FStar_Format.parens doc1

and (doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____65513 =
          let uu____65520 = as_uni_op p  in FStar_Option.get uu____65520  in
        match uu____65513 with
        | (uu____65535,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11]
               in
            FStar_Format.parens doc1

and (doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____65548 = string_of_mlconstant c  in
          FStar_Format.text uu____65548
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____65584 =
            match uu____65584 with
            | (name,p) ->
                let uu____65594 =
                  let uu____65597 =
                    let uu____65598 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____65598  in
                  let uu____65604 =
                    let uu____65607 =
                      let uu____65610 = doc_of_pattern currentModule p  in
                      [uu____65610]  in
                    (FStar_Format.text "=") :: uu____65607  in
                  uu____65597 :: uu____65604  in
                FStar_Format.reduce1 uu____65594
             in
          let uu____65612 =
            let uu____65613 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____65613  in
          FStar_Format.cbrackets uu____65612
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____65627 = is_standard_constructor ctor  in
            if uu____65627
            then
              let uu____65631 =
                let uu____65638 = as_standard_constructor ctor  in
                FStar_Option.get uu____65638  in
              FStar_Pervasives_Native.snd uu____65631
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____65665 = is_standard_constructor ctor  in
            if uu____65665
            then
              let uu____65669 =
                let uu____65676 = as_standard_constructor ctor  in
                FStar_Option.get uu____65676  in
              FStar_Pervasives_Native.snd uu____65669
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____65705 =
                  let uu____65708 =
                    let uu____65709 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____65709  in
                  let uu____65710 =
                    let uu____65713 =
                      let uu____65716 = doc_of_pattern currentModule xs  in
                      [uu____65716]  in
                    (FStar_Format.text "::") :: uu____65713  in
                  uu____65708 :: uu____65710  in
                FStar_Format.reduce uu____65705
            | (uu____65718,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____65719)::[]) ->
                let uu____65726 =
                  let uu____65729 =
                    let uu____65732 =
                      let uu____65733 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____65733  in
                    [uu____65732]  in
                  (FStar_Format.text name) :: uu____65729  in
                FStar_Format.reduce1 uu____65726
            | uu____65734 ->
                let uu____65742 =
                  let uu____65745 =
                    let uu____65748 =
                      let uu____65749 =
                        let uu____65750 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____65750
                         in
                      FStar_Format.parens uu____65749  in
                    [uu____65748]  in
                  (FStar_Format.text name) :: uu____65745  in
                FStar_Format.reduce1 uu____65742
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____65765 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____65765
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65778  ->
      match uu____65778 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____65788 =
                  let uu____65791 =
                    let uu____65794 = doc_of_pattern currentModule p  in
                    [uu____65794]  in
                  (FStar_Format.text "|") :: uu____65791  in
                FStar_Format.reduce1 uu____65788
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____65798 =
                  let uu____65801 =
                    let uu____65804 = doc_of_pattern currentModule p  in
                    [uu____65804; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____65801  in
                FStar_Format.reduce1 uu____65798
             in
          let uu____65807 =
            let uu____65810 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____65813 =
              let uu____65816 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____65816; FStar_Format.text "end"]  in
            uu____65810 :: uu____65813  in
          FStar_Format.combine FStar_Format.hardline uu____65807

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65819  ->
      match uu____65819 with
      | (rec_,top_level,lets) ->
          let for1 uu____65844 =
            match uu____65844 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____65847;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____65849;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____65865 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____65865
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____65868::uu____65869,uu____65870) ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.None  ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty
                              in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1]
                          | FStar_Pervasives_Native.Some (vs,ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              let vars =
                                let uu____65894 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____65894
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____65913 =
                  let uu____65916 =
                    let uu____65919 = FStar_Format.reduce1 ids  in
                    [uu____65919; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____65916  in
                FStar_Format.reduce1 uu____65913
             in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then
              FStar_Format.reduce1
                [FStar_Format.text "let"; FStar_Format.text "rec"]
            else FStar_Format.text "let"  in
          let lets1 = FStar_List.map for1 lets  in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   FStar_Format.reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else FStar_Format.text "and";
                     doc1]) lets1
             in
          FStar_Format.combine FStar_Format.hardline lets2

and (doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc) =
  fun uu____65945  ->
    match uu____65945 with
    | (lineno,file) ->
        let uu____65952 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____65952
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))])

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____66004 =
        match uu____66004 with
        | (uu____66027,x,mangle_opt,tparams,uu____66031,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____66066 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____66077 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____66077
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____66104 =
                    match uu____66104 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____66117 =
                    let uu____66118 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____66118
                     in
                  FStar_Format.cbrackets uu____66117
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____66159 =
                    match uu____66159 with
                    | (name,tys) ->
                        let uu____66190 = FStar_List.split tys  in
                        (match uu____66190 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____66213 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1
                                     in
                                  let tys3 =
                                    FStar_Format.combine
                                      (FStar_Format.text " * ") tys2
                                     in
                                  FStar_Format.reduce1
                                    [FStar_Format.text name;
                                    FStar_Format.text "of";
                                    tys3]))
                     in
                  let ctors1 = FStar_List.map forctor ctors  in
                  let ctors2 =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors1
                     in
                  FStar_Format.combine FStar_Format.hardline ctors2
               in
            let doc1 =
              let uu____66244 =
                let uu____66247 =
                  let uu____66250 =
                    let uu____66251 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____66251  in
                  [uu____66250]  in
                tparams1 :: uu____66247  in
              FStar_Format.reduce1 uu____66244  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____66260 =
                   let uu____66263 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____66263; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____66260)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____66271 =
            let uu____66274 =
              let uu____66277 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____66277]  in
            (FStar_Format.text "type") :: uu____66274  in
          FStar_Format.reduce1 uu____66271
        else FStar_Format.text ""  in
      doc2
  
let rec (doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____66313 =
            let uu____66316 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____66319 =
              let uu____66322 = doc_of_sig currentModule subsig  in
              let uu____66323 =
                let uu____66326 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____66326]  in
              uu____66322 :: uu____66323  in
            uu____66316 :: uu____66319  in
          FStar_Format.combine FStar_Format.hardline uu____66313
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____66346 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____66346  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____66351,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
             in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls

and (doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun s  ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s  in
      let docs1 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs
         in
      FStar_Format.reduce docs1

let (doc_of_mod1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun m  ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,args) ->
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args  in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1
             in
          let args3 =
            let uu____66430 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____66430  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____66446 =
            let uu____66449 =
              let uu____66452 =
                let uu____66455 =
                  let uu____66458 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____66458]  in
                (FStar_Format.text "=") :: uu____66455  in
              (FStar_Format.text "_") :: uu____66452  in
            (FStar_Format.text "let") :: uu____66449  in
          FStar_Format.reduce1 uu____66446
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
  
let (doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x  in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____66488 ->
                  FStar_Format.empty
              | uu____66489 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____66502  ->
    match uu____66502 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____66572 =
          match uu____66572 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head1 =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x1;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"]
                 in
              let tail1 = FStar_Format.reduce1 [FStar_Format.text "end"]  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66632  ->
                     match uu____66632 with
                     | (s,uu____66638) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____66659 =
                let uu____66662 =
                  let uu____66665 =
                    let uu____66668 = FStar_Format.reduce sub3  in
                    [uu____66668;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____66665
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____66662
                 in
              FStar_Format.reduce uu____66659
        
        and for1_mod istop uu____66671 =
          match uu____66671 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____66753 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____66774 =
                  let uu____66777 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____66777
                  then
                    [FStar_Format.text "module";
                    FStar_Format.text target_mod_name]
                  else
                    if Prims.op_Negation istop
                    then
                      [FStar_Format.text "module";
                      FStar_Format.text target_mod_name;
                      FStar_Format.text "=";
                      FStar_Format.text "struct"]
                    else []
                   in
                FStar_Format.reduce1 uu____66774  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66808  ->
                     match uu____66808 with
                     | (uu____66813,m) -> doc_of_mod target_mod_name m)
                  sigmod
                 in
              let sub2 = FStar_List.map (for1_mod false) sub1  in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let prefix1 =
                let uu____66839 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____66839
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____66847 =
                let uu____66850 =
                  let uu____66853 =
                    let uu____66856 =
                      let uu____66859 =
                        let uu____66862 =
                          let uu____66865 = FStar_Format.reduce sub3  in
                          [uu____66865;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____66862
                         in
                      FStar_Format.hardline :: uu____66859  in
                    FStar_List.append maybe_open_pervasives uu____66856  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____66853
                   in
                FStar_List.append prefix1 uu____66850  in
              FStar_All.pipe_left FStar_Format.reduce uu____66847
         in
        let docs =
          FStar_List.map
            (fun uu____66909  ->
               match uu____66909 with
               | (x,s,m) ->
                   let uu____66966 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____66968 = for1_mod true (x, s, m)  in
                   (uu____66966, uu____66968)) mllib
           in
        docs
  
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  = fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67011 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____67011 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67027 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____67027 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  