open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | ILeft  -> true | uu____6 -> false 
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____12 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____18 -> false 
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Right  -> true | uu____24 -> false 
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____30 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____41 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____47 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____54 -> false
  
let (__proj__Infix__item___0 : fixity -> assoc) =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
let (t_prio_fun : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "10"), (Infix Right)) 
let (t_prio_tpl : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let (t_prio_name : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "30"), Postfix) 
let (e_bin_prio_lambda : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "5"), Prefix) 
let (e_bin_prio_if : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "15"), Prefix) 
let (e_bin_prio_letin : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "19"), Prefix) 
let (e_bin_prio_or : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "20"), (Infix Left)) 
let (e_bin_prio_and : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "25"), (Infix Left)) 
let (e_bin_prio_eq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let (e_bin_prio_order : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let (e_bin_prio_op1 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "30"), (Infix Left)) 
let (e_bin_prio_op2 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "40"), (Infix Left)) 
let (e_bin_prio_op3 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "50"), (Infix Left)) 
let (e_bin_prio_op4 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "60"), (Infix Left)) 
let (e_bin_prio_comb : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "70"), (Infix Left)) 
let (e_bin_prio_seq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "100"), (Infix Left)) 
let (e_app_prio : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "10000"), (Infix Left)) 
let (min_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let (max_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns :
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool
  =
  fun x  ->
    match x with
    | ([],uu____173) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____196,uu____197) -> false
  
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
                  let uu____259 = FStar_Util.first_N cg_len ns  in
                  match uu____259 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____292 =
                           let uu____295 =
                             let uu____298 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____298]  in
                           FStar_List.append pfx uu____295  in
                         FStar_Pervasives_Native.Some uu____292
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
      let uu____326 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____326 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____331 ->
          let uu____332 = x  in
          (match uu____332 with
           | (ns,x1) ->
               let uu____339 = path_of_ns currentModule ns  in
               (uu____339, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____349 =
      let uu____350 =
        let uu____352 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____352  in
      let uu____354 = FStar_String.get s (Prims.parse_int "0")  in
      uu____350 <> uu____354  in
    if uu____349 then Prims.strcat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____373 = mlpath_of_mlpath currentModule mlp  in
         match uu____373 with
         | (p,s) ->
             let uu____380 =
               let uu____383 =
                 let uu____386 = ptsym_of_symbol s  in [uu____386]  in
               FStar_List.append p uu____383  in
             FStar_String.concat "." uu____380)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____397 = mlpath_of_mlpath currentModule mlp  in
      match uu____397 with
      | (p,s) ->
          let s1 =
            let uu____405 =
              let uu____406 =
                let uu____408 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____408  in
              let uu____410 = FStar_String.get s (Prims.parse_int "0")  in
              uu____406 <> uu____410  in
            if uu____405 then Prims.strcat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
  
let (infix_prim_ops :
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list)
  =
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
let (prim_uni_ops :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____642  ->
    let op_minus =
      let uu____644 =
        let uu____645 = FStar_Options.codegen ()  in
        uu____645 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____644 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____669 . unit -> 'Auu____669 Prims.list =
  fun uu____672  -> [] 
let (prim_constructors :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let (is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool) =
  fun ns  -> ns = ["Prims"] 
let (as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
      FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun uu____726  ->
    match uu____726 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____771  ->
               match uu____771 with | (y,uu____783,uu____784) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____809 = as_bin_op p  in uu____809 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____854  ->
    match uu____854 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____873 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____887  -> match uu____887 with | (y,uu____893) -> x = y)
            uu____873
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____904 = as_uni_op p  in uu____904 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____936  ->
    match uu____936 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____962  -> match uu____962 with | (y,uu____968) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____979 = as_standard_constructor p  in
    uu____979 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____1020  ->
    fun inner  ->
      fun doc1  ->
        match uu____1020 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1077 = _inner  in
              match uu____1077 with
              | (pi,fi) ->
                  let uu____1084 = _outer  in
                  (match uu____1084 with
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
                           | (uu____1091,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1092,uu____1093) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___256_1123  ->
      if uu___256_1123 = 92
      then "\\\\"
      else
        if uu___256_1123 = 32
        then " "
        else
          if uu___256_1123 = 8
          then "\\b"
          else
            if uu___256_1123 = 9
            then "\\t"
            else
              if uu___256_1123 = 13
              then "\\r"
              else
                if uu___256_1123 = 10
                then "\\n"
                else
                  if uu___256_1123 = 39
                  then "\\'"
                  else
                    if uu___256_1123 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___256_1123
                      then FStar_Util.string_of_char uu___256_1123
                      else
                        if FStar_Util.is_punctuation uu___256_1123
                        then FStar_Util.string_of_char uu___256_1123
                        else
                          if FStar_Util.is_symbol uu___256_1123
                          then FStar_Util.string_of_char uu___256_1123
                          else fallback uu___256_1123
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1152 = FStar_Util.string_of_int nc  in
        Prims.strcat uu____1152
          (if
             ((nc >= (Prims.parse_int "32")) &&
                (nc <= (Prims.parse_int "127")))
               && (nc <> (Prims.parse_int "34"))
           then
             Prims.strcat " (*"
               (Prims.strcat (FStar_Util.string_of_char c) "*)")
           else "")
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1199,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1211,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1238 =
          let uu____1239 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat uu____1239 "\""  in
        Prims.strcat "\"" uu____1238
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1241 =
          let uu____1242 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat uu____1242 "\""  in
        Prims.strcat "\"" uu____1241
    | uu____1243 ->
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
              let uu____1288 =
                let uu____1289 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____1289  in
              FStar_Format.parens uu____1288  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1310 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____1316 =
                    let uu____1317 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____1317  in
                  FStar_Format.parens uu____1316
               in
            let name1 = ptsym currentModule name  in
            let uu____1319 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____1319
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1321,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____1325 =
              let uu____1326 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____1326  in
            maybe_paren outer t_prio_fun uu____1325
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1327 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1327
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
        let uu____1332 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____1332

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
            let uu____1416 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1416
            then
              let uu____1417 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____1417
            else
              (let uu____1419 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____1419)
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
            let uu____1431 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____1431
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1433 = string_of_mlconstant c  in
            FStar_Format.text uu____1433
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1436 = ptsym currentModule path  in
            FStar_Format.text uu____1436
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1464 =
              match uu____1464 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1472 =
                    let uu____1475 =
                      let uu____1476 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____1476  in
                    [uu____1475; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____1472
               in
            let uu____1479 =
              let uu____1480 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____1480  in
            FStar_Format.cbrackets uu____1479
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1503 = is_standard_constructor ctor  in
              if uu____1503
              then
                let uu____1504 =
                  let uu____1509 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1509  in
                FStar_Pervasives_Native.snd uu____1504
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1540 = is_standard_constructor ctor  in
              if uu____1540
              then
                let uu____1541 =
                  let uu____1546 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1546  in
                FStar_Pervasives_Native.snd uu____1541
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
              | (uu____1568,uu____1569) ->
                  let uu____1574 =
                    let uu____1577 =
                      let uu____1580 =
                        let uu____1581 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____1581  in
                      [uu____1580]  in
                    (FStar_Format.text name) :: uu____1577  in
                  FStar_Format.reduce1 uu____1574
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____1591 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____1591) es
               in
            let docs1 =
              let uu____1593 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____1593  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1608 =
                  let uu____1611 =
                    let uu____1614 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____1614]  in
                  FStar_Format.hardline :: uu____1611  in
                FStar_Format.reduce uu____1608
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____1620 =
              let uu____1621 =
                let uu____1624 =
                  let uu____1627 =
                    let uu____1630 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____1630]  in
                  doc1 :: uu____1627  in
                pre :: uu____1624  in
              FStar_Format.combine FStar_Format.hardline uu____1621  in
            FStar_Format.parens uu____1620
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1640::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1642;
                    FStar_Extraction_ML_Syntax.loc = uu____1643;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1645)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1647;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1648;_}::[])
                 when
                 let uu____1683 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____1683 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1706;
                            FStar_Extraction_ML_Syntax.loc = uu____1707;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1709;
                       FStar_Extraction_ML_Syntax.loc = uu____1710;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1766;
                   FStar_Extraction_ML_Syntax.loc = uu____1767;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1780;
                   FStar_Extraction_ML_Syntax.loc = uu____1781;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1788 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____1799 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____1799)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____1816 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1816
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1820 =
                   let uu____1823 =
                     let uu____1826 =
                       let uu____1829 =
                         let uu____1830 = ptsym currentModule f  in
                         FStar_Format.text uu____1830  in
                       [uu____1829]  in
                     (FStar_Format.text ".") :: uu____1826  in
                   e2 :: uu____1823  in
                 FStar_Format.reduce uu____1820)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1860 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1860
              then
                let uu____1861 =
                  let uu____1864 =
                    let uu____1867 =
                      let uu____1870 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1872 =
                              let uu____1875 =
                                let uu____1878 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____1878]  in
                              (FStar_Format.text " : ") :: uu____1875  in
                            FStar_Format.reduce1 uu____1872
                        | uu____1879 -> FStar_Format.text ""  in
                      [uu____1870; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____1867  in
                  (FStar_Format.text "(") :: uu____1864  in
                FStar_Format.reduce1 uu____1861
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____1893  ->
                   match uu____1893 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____1902 =
                let uu____1905 =
                  let uu____1908 = FStar_Format.reduce1 ids1  in
                  [uu____1908; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____1905  in
              FStar_Format.reduce1 uu____1902  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1915 =
                let uu____1918 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1919 =
                  let uu____1922 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____1922; FStar_Format.text "end"]  in
                uu____1918 :: uu____1919  in
              FStar_Format.combine FStar_Format.hardline uu____1915  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1930 =
                let uu____1933 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1934 =
                  let uu____1937 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1938 =
                    let uu____1941 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____1942 =
                      let uu____1945 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____1945; FStar_Format.text "end"]  in
                    uu____1941 :: uu____1942  in
                  uu____1937 :: uu____1938  in
                uu____1933 :: uu____1934  in
              FStar_Format.combine FStar_Format.hardline uu____1930  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____1983 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____1983 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2000 =
              let uu____2003 =
                let uu____2006 =
                  let uu____2007 = ptctor currentModule exn  in
                  FStar_Format.text uu____2007  in
                [uu____2006]  in
              (FStar_Format.text "raise") :: uu____2003  in
            FStar_Format.reduce1 uu____2000
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2029 =
              let uu____2032 =
                let uu____2035 =
                  let uu____2036 = ptctor currentModule exn  in
                  FStar_Format.text uu____2036  in
                let uu____2037 =
                  let uu____2040 =
                    let uu____2041 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____2041  in
                  [uu____2040]  in
                uu____2035 :: uu____2037  in
              (FStar_Format.text "raise") :: uu____2032  in
            FStar_Format.reduce1 uu____2029
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2064 =
              let uu____2067 =
                let uu____2070 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2071 =
                  let uu____2074 =
                    let uu____2077 =
                      let uu____2078 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____2078
                       in
                    [uu____2077]  in
                  (FStar_Format.text "with") :: uu____2074  in
                uu____2070 :: uu____2071  in
              (FStar_Format.text "try") :: uu____2067  in
            FStar_Format.combine FStar_Format.hardline uu____2064
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
          let uu____2099 =
            let uu____2110 = as_bin_op p  in FStar_Option.get uu____2110  in
          match uu____2099 with
          | (uu____2133,prio,txt) ->
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
        let uu____2150 =
          let uu____2155 = as_uni_op p  in FStar_Option.get uu____2155  in
        match uu____2150 with
        | (uu____2166,txt) ->
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
          let uu____2173 = string_of_mlconstant c  in
          FStar_Format.text uu____2173
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2202 =
            match uu____2202 with
            | (name,p) ->
                let uu____2209 =
                  let uu____2212 =
                    let uu____2213 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2213  in
                  let uu____2216 =
                    let uu____2219 =
                      let uu____2222 = doc_of_pattern currentModule p  in
                      [uu____2222]  in
                    (FStar_Format.text "=") :: uu____2219  in
                  uu____2212 :: uu____2216  in
                FStar_Format.reduce1 uu____2209
             in
          let uu____2223 =
            let uu____2224 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____2224  in
          FStar_Format.cbrackets uu____2223
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2247 = is_standard_constructor ctor  in
            if uu____2247
            then
              let uu____2248 =
                let uu____2253 = as_standard_constructor ctor  in
                FStar_Option.get uu____2253  in
              FStar_Pervasives_Native.snd uu____2248
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2284 = is_standard_constructor ctor  in
            if uu____2284
            then
              let uu____2285 =
                let uu____2290 = as_standard_constructor ctor  in
                FStar_Option.get uu____2290  in
              FStar_Pervasives_Native.snd uu____2285
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2309 =
                  let uu____2312 =
                    let uu____2313 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____2313  in
                  let uu____2314 =
                    let uu____2317 =
                      let uu____2320 = doc_of_pattern currentModule xs  in
                      [uu____2320]  in
                    (FStar_Format.text "::") :: uu____2317  in
                  uu____2312 :: uu____2314  in
                FStar_Format.reduce uu____2309
            | (uu____2321,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2322)::[]) ->
                let uu____2327 =
                  let uu____2330 =
                    let uu____2333 =
                      let uu____2334 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____2334  in
                    [uu____2333]  in
                  (FStar_Format.text name) :: uu____2330  in
                FStar_Format.reduce1 uu____2327
            | uu____2335 ->
                let uu____2342 =
                  let uu____2345 =
                    let uu____2348 =
                      let uu____2349 =
                        let uu____2350 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2350
                         in
                      FStar_Format.parens uu____2349  in
                    [uu____2348]  in
                  (FStar_Format.text name) :: uu____2345  in
                FStar_Format.reduce1 uu____2342
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____2363 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____2363
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____2374  ->
      match uu____2374 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2383 =
                  let uu____2386 =
                    let uu____2389 = doc_of_pattern currentModule p  in
                    [uu____2389]  in
                  (FStar_Format.text "|") :: uu____2386  in
                FStar_Format.reduce1 uu____2383
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____2392 =
                  let uu____2395 =
                    let uu____2398 = doc_of_pattern currentModule p  in
                    [uu____2398; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____2395  in
                FStar_Format.reduce1 uu____2392
             in
          let uu____2399 =
            let uu____2402 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____2403 =
              let uu____2406 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____2406; FStar_Format.text "end"]  in
            uu____2402 :: uu____2403  in
          FStar_Format.combine FStar_Format.hardline uu____2399

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____2408  ->
      match uu____2408 with
      | (rec_,top_level,lets) ->
          let for1 uu____2429 =
            match uu____2429 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2432;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____2434;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2444 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____2444
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2445::uu____2446,uu____2447) ->
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
                                let uu____2505 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____2505
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____2517 =
                  let uu____2520 =
                    let uu____2523 = FStar_Format.reduce1 ids  in
                    [uu____2523; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____2520  in
                FStar_Format.reduce1 uu____2517
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
  fun uu____2537  ->
    match uu____2537 with
    | (lineno,file) ->
        let uu____2540 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____2540
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____2576 =
        match uu____2576 with
        | (uu____2595,x,mangle_opt,tparams,uu____2599,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2617 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____2625 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____2625
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2649 =
                    match uu____2649 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____2658 =
                    let uu____2659 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2659
                     in
                  FStar_Format.cbrackets uu____2658
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2694 =
                    match uu____2694 with
                    | (name,tys) ->
                        let uu____2719 = FStar_List.split tys  in
                        (match uu____2719 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2738 ->
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
              let uu____2764 =
                let uu____2767 =
                  let uu____2770 =
                    let uu____2771 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____2771  in
                  [uu____2770]  in
                tparams1 :: uu____2767  in
              FStar_Format.reduce1 uu____2764  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____2776 =
                   let uu____2779 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____2779; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____2776)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2784 =
            let uu____2787 =
              let uu____2790 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____2790]  in
            (FStar_Format.text "type") :: uu____2787  in
          FStar_Format.reduce1 uu____2784
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
          let uu____2816 =
            let uu____2819 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____2820 =
              let uu____2823 = doc_of_sig currentModule subsig  in
              let uu____2824 =
                let uu____2827 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____2827]  in
              uu____2823 :: uu____2824  in
            uu____2819 :: uu____2820  in
          FStar_Format.combine FStar_Format.hardline uu____2816
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____2841 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____2841  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2843,ty)) ->
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
            let uu____2913 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____2913  in
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
          let uu____2924 =
            let uu____2927 =
              let uu____2930 =
                let uu____2933 =
                  let uu____2936 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____2936]  in
                (FStar_Format.text "=") :: uu____2933  in
              (FStar_Format.text "_") :: uu____2930  in
            (FStar_Format.text "let") :: uu____2927  in
          FStar_Format.reduce1 uu____2924
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2960 ->
                  FStar_Format.empty
              | uu____2961 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____2972  ->
    match uu____2972 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3038 =
          match uu____3038 with
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
                  (fun uu____3093  ->
                     match uu____3093 with
                     | (s,uu____3099) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____3120 =
                let uu____3123 =
                  let uu____3126 =
                    let uu____3129 = FStar_Format.reduce sub3  in
                    [uu____3129;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3126
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3123
                 in
              FStar_Format.reduce uu____3120
        
        and for1_mod istop uu____3132 =
          match uu____3132 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3200 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)]
                 in
              let head1 =
                let uu____3211 =
                  let uu____3214 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____3214
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
                FStar_Format.reduce1 uu____3211  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____3233  ->
                     match uu____3233 with
                     | (uu____3238,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____3263 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____3263
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____3267 =
                let uu____3270 =
                  let uu____3273 =
                    let uu____3276 =
                      let uu____3279 =
                        let uu____3282 =
                          let uu____3285 = FStar_Format.reduce sub3  in
                          [uu____3285;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3282
                         in
                      FStar_Format.hardline :: uu____3279  in
                    FStar_List.append maybe_open_pervasives uu____3276  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3273
                   in
                FStar_List.append prefix1 uu____3270  in
              FStar_All.pipe_left FStar_Format.reduce uu____3267
         in
        let docs =
          FStar_List.map
            (fun uu____3324  ->
               match uu____3324 with
               | (x,s,m) ->
                   let uu____3374 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____3375 = for1_mod true (x, s, m)  in
                   (uu____3374, uu____3375)) mllib
           in
        docs
  
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3410 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____3410 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3422 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____3422 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  