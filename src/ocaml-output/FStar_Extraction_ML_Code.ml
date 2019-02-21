open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | ILeft  -> true | uu____9 -> false 
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____20 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____31 -> false 
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Right  -> true | uu____42 -> false 
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____53 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____69 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____80 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____92 -> false
  
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
    | ([],uu____290) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____314,uu____315) -> false
  
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
                  let uu____400 = FStar_Util.first_N cg_len ns  in
                  match uu____400 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____444 =
                           let uu____448 =
                             let uu____452 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____452]  in
                           FStar_List.append pfx uu____448  in
                         FStar_Pervasives_Native.Some uu____444
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
      let uu____498 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____498 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____514 ->
          let uu____516 = x  in
          (match uu____516 with
           | (ns,x1) ->
               let uu____527 = path_of_ns currentModule ns  in
               (uu____527, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____545 =
      let uu____547 =
        let uu____549 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____549  in
      let uu____552 = FStar_String.get s (Prims.parse_int "0")  in
      uu____547 <> uu____552  in
    if uu____545 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____588 = mlpath_of_mlpath currentModule mlp  in
         match uu____588 with
         | (p,s) ->
             let uu____600 =
               let uu____604 =
                 let uu____608 = ptsym_of_symbol s  in [uu____608]  in
               FStar_List.append p uu____604  in
             FStar_String.concat "." uu____600)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____629 = mlpath_of_mlpath currentModule mlp  in
      match uu____629 with
      | (p,s) ->
          let s1 =
            let uu____643 =
              let uu____645 =
                let uu____647 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____647  in
              let uu____650 = FStar_String.get s (Prims.parse_int "0")  in
              uu____645 <> uu____650  in
            if uu____643 then Prims.op_Hat "U__" s else s  in
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
  fun uu____1013  ->
    let op_minus =
      let uu____1016 =
        let uu____1018 = FStar_Options.codegen ()  in
        uu____1018 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____1016 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____1067 . unit -> 'Auu____1067 Prims.list =
  fun uu____1070  -> [] 
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
  fun uu____1165  ->
    match uu____1165 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1224  ->
               match uu____1224 with | (y,uu____1240,uu____1241) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1279 = as_bin_op p  in
    uu____1279 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1336  ->
    match uu____1336 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____1364 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____1382  ->
               match uu____1382 with | (y,uu____1391) -> x = y) uu____1364
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1412 = as_uni_op p  in
    uu____1412 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1456  ->
    match uu____1456 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1493  ->
               match uu____1493 with | (y,uu____1502) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1523 = as_standard_constructor p  in
    uu____1523 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____1573  ->
    fun inner  ->
      fun doc1  ->
        match uu____1573 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1639 = _inner  in
              match uu____1639 with
              | (pi,fi) ->
                  let uu____1650 = _outer  in
                  (match uu____1650 with
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
                           | (uu____1668,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1670,uu____1671) -> false)))
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
    fun uu___31_1710  ->
      if uu___31_1710 = 92
      then "\\\\"
      else
        if uu___31_1710 = 32
        then " "
        else
          if uu___31_1710 = 8
          then "\\b"
          else
            if uu___31_1710 = 9
            then "\\t"
            else
              if uu___31_1710 = 13
              then "\\r"
              else
                if uu___31_1710 = 10
                then "\\n"
                else
                  if uu___31_1710 = 39
                  then "\\'"
                  else
                    if uu___31_1710 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___31_1710
                      then FStar_Util.string_of_char uu___31_1710
                      else
                        if FStar_Util.is_punctuation uu___31_1710
                        then FStar_Util.string_of_char uu___31_1710
                        else
                          if FStar_Util.is_symbol uu___31_1710
                          then FStar_Util.string_of_char uu___31_1710
                          else fallback uu___31_1710
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1757 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____1757
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
        (s,FStar_Pervasives_Native.Some (uu____1821,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1835,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1867 =
          let uu____1869 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____1869 "\""  in
        Prims.op_Hat "\"" uu____1867
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1875 =
          let uu____1877 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____1877 "\""  in
        Prims.op_Hat "\"" uu____1875
    | uu____1881 ->
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
              let uu____1940 =
                let uu____1941 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____1941  in
              FStar_Format.parens uu____1940  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1951 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____1957 =
                    let uu____1958 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____1958  in
                  FStar_Format.parens uu____1957
               in
            let name1 = ptsym currentModule name  in
            let uu____1962 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____1962
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1964,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____1968 =
              let uu____1969 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____1969  in
            maybe_paren outer t_prio_fun uu____1968
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1971 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1971
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
        let uu____1983 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____1983

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
            let uu____2076 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2076
            then
              let uu____2079 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____2079
            else
              (let uu____2083 =
                 let uu____2084 =
                   let uu____2087 =
                     let uu____2090 = FStar_Format.parens doc1  in
                     [uu____2090]  in
                   (FStar_Format.text "Obj.magic ") :: uu____2087  in
                 FStar_Format.reduce uu____2084  in
               FStar_Format.parens uu____2083)
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
            let uu____2104 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____2104
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2106 = string_of_mlconstant c  in
            FStar_Format.text uu____2106
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2111 = ptsym currentModule path  in
            FStar_Format.text uu____2111
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2145 =
              match uu____2145 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2156 =
                    let uu____2159 =
                      let uu____2160 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____2160  in
                    [uu____2159; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____2156
               in
            let uu____2167 =
              let uu____2168 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____2168  in
            FStar_Format.cbrackets uu____2167
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2182 = is_standard_constructor ctor  in
              if uu____2182
              then
                let uu____2186 =
                  let uu____2193 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2193  in
                FStar_Pervasives_Native.snd uu____2186
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2220 = is_standard_constructor ctor  in
              if uu____2220
              then
                let uu____2224 =
                  let uu____2231 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2231  in
                FStar_Pervasives_Native.snd uu____2224
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  let uu____2263 =
                    let uu____2266 = FStar_Format.parens x  in
                    [uu____2266; FStar_Format.text "::"; xs]  in
                  FStar_Format.reduce uu____2263
              | (uu____2268,uu____2269) ->
                  let uu____2276 =
                    let uu____2279 =
                      let uu____2282 =
                        let uu____2283 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____2283  in
                      [uu____2282]  in
                    (FStar_Format.text name) :: uu____2279  in
                  FStar_Format.reduce1 uu____2276
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2294 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____2294) es
               in
            let docs1 =
              let uu____2296 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____2296  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2313 =
                  let uu____2316 =
                    let uu____2319 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2319]  in
                  FStar_Format.hardline :: uu____2316  in
                FStar_Format.reduce uu____2313
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2328 =
              let uu____2329 =
                let uu____2332 =
                  let uu____2335 =
                    let uu____2338 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____2338]  in
                  doc1 :: uu____2335  in
                pre :: uu____2332  in
              FStar_Format.combine FStar_Format.hardline uu____2329  in
            FStar_Format.parens uu____2328
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2349::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2351;
                    FStar_Extraction_ML_Syntax.loc = uu____2352;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2354)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2356;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2357;_}::[])
                 when
                 let uu____2401 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2401 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2427;
                            FStar_Extraction_ML_Syntax.loc = uu____2428;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2430;
                       FStar_Extraction_ML_Syntax.loc = uu____2431;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2489;
                   FStar_Extraction_ML_Syntax.loc = uu____2490;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2503;
                   FStar_Extraction_ML_Syntax.loc = uu____2504;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2511 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2522 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____2522)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____2527 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2527
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2537 =
                   let uu____2540 =
                     let uu____2543 =
                       let uu____2546 =
                         let uu____2547 = ptsym currentModule f  in
                         FStar_Format.text uu____2547  in
                       [uu____2546]  in
                     (FStar_Format.text ".") :: uu____2543  in
                   e2 :: uu____2540  in
                 FStar_Format.reduce uu____2537)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2583 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2583
              then
                let uu____2586 =
                  let uu____2589 =
                    let uu____2592 =
                      let uu____2595 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2597 =
                              let uu____2600 =
                                let uu____2603 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2603]  in
                              (FStar_Format.text " : ") :: uu____2600  in
                            FStar_Format.reduce1 uu____2597
                        | uu____2605 -> FStar_Format.text ""  in
                      [uu____2595; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____2592  in
                  (FStar_Format.text "(") :: uu____2589  in
                FStar_Format.reduce1 uu____2586
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2624  ->
                   match uu____2624 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____2636 =
                let uu____2639 =
                  let uu____2642 = FStar_Format.reduce1 ids1  in
                  [uu____2642; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____2639  in
              FStar_Format.reduce1 uu____2636  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2651 =
                let uu____2654 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____2658 =
                  let uu____2661 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2661; FStar_Format.text "end"]  in
                uu____2654 :: uu____2658  in
              FStar_Format.combine FStar_Format.hardline uu____2651  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2670 =
                let uu____2673 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____2677 =
                  let uu____2680 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2681 =
                    let uu____2684 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____2688 =
                      let uu____2691 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2691; FStar_Format.text "end"]  in
                    uu____2684 :: uu____2688  in
                  uu____2680 :: uu____2681  in
                uu____2673 :: uu____2677  in
              FStar_Format.combine FStar_Format.hardline uu____2670  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2730 =
                let uu____2731 =
                  let uu____2734 =
                    let uu____2737 = FStar_Format.parens cond1  in
                    [uu____2737; FStar_Format.text "with"]  in
                  (FStar_Format.text "match") :: uu____2734  in
                FStar_Format.reduce1 uu____2731  in
              uu____2730 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2744 =
              let uu____2747 =
                let uu____2750 =
                  let uu____2751 = ptctor currentModule exn  in
                  FStar_Format.text uu____2751  in
                [uu____2750]  in
              (FStar_Format.text "raise") :: uu____2747  in
            FStar_Format.reduce1 uu____2744
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2763 =
              let uu____2766 =
                let uu____2769 =
                  let uu____2770 = ptctor currentModule exn  in
                  FStar_Format.text uu____2770  in
                let uu____2772 =
                  let uu____2775 =
                    let uu____2776 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____2776  in
                  [uu____2775]  in
                uu____2769 :: uu____2772  in
              (FStar_Format.text "raise") :: uu____2766  in
            FStar_Format.reduce1 uu____2763
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2801 =
              let uu____2804 =
                let uu____2807 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2808 =
                  let uu____2811 =
                    let uu____2814 =
                      let uu____2815 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____2815
                       in
                    [uu____2814]  in
                  (FStar_Format.text "with") :: uu____2811  in
                uu____2807 :: uu____2808  in
              (FStar_Format.text "try") :: uu____2804  in
            FStar_Format.combine FStar_Format.hardline uu____2801
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
          let uu____2839 =
            let uu____2853 = as_bin_op p  in FStar_Option.get uu____2853  in
          match uu____2839 with
          | (uu____2882,prio,txt) ->
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
        let uu____2906 =
          let uu____2913 = as_uni_op p  in FStar_Option.get uu____2913  in
        match uu____2906 with
        | (uu____2928,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 =
              let uu____2936 =
                let uu____2939 =
                  let uu____2942 = FStar_Format.parens e11  in [uu____2942]
                   in
                (FStar_Format.text txt) :: uu____2939  in
              FStar_Format.reduce1 uu____2936  in
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
          let uu____2948 = string_of_mlconstant c  in
          FStar_Format.text uu____2948
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2984 =
            match uu____2984 with
            | (name,p) ->
                let uu____2994 =
                  let uu____2997 =
                    let uu____2998 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2998  in
                  let uu____3004 =
                    let uu____3007 =
                      let uu____3010 = doc_of_pattern currentModule p  in
                      [uu____3010]  in
                    (FStar_Format.text "=") :: uu____3007  in
                  uu____2997 :: uu____3004  in
                FStar_Format.reduce1 uu____2994
             in
          let uu____3012 =
            let uu____3013 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____3013  in
          FStar_Format.cbrackets uu____3012
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____3027 = is_standard_constructor ctor  in
            if uu____3027
            then
              let uu____3031 =
                let uu____3038 = as_standard_constructor ctor  in
                FStar_Option.get uu____3038  in
              FStar_Pervasives_Native.snd uu____3031
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3065 = is_standard_constructor ctor  in
            if uu____3065
            then
              let uu____3069 =
                let uu____3076 = as_standard_constructor ctor  in
                FStar_Option.get uu____3076  in
              FStar_Pervasives_Native.snd uu____3069
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3105 =
                  let uu____3108 =
                    let uu____3109 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____3109  in
                  let uu____3110 =
                    let uu____3113 =
                      let uu____3116 = doc_of_pattern currentModule xs  in
                      [uu____3116]  in
                    (FStar_Format.text "::") :: uu____3113  in
                  uu____3108 :: uu____3110  in
                FStar_Format.reduce uu____3105
            | (uu____3118,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3119)::[]) ->
                let uu____3126 =
                  let uu____3129 =
                    let uu____3132 =
                      let uu____3133 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3133  in
                    [uu____3132]  in
                  (FStar_Format.text name) :: uu____3129  in
                FStar_Format.reduce1 uu____3126
            | uu____3134 ->
                let uu____3142 =
                  let uu____3145 =
                    let uu____3148 =
                      let uu____3149 =
                        let uu____3150 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____3150
                         in
                      FStar_Format.parens uu____3149  in
                    [uu____3148]  in
                  (FStar_Format.text name) :: uu____3145  in
                FStar_Format.reduce1 uu____3142
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3165 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____3165
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____3178  ->
      match uu____3178 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3188 =
                  let uu____3191 =
                    let uu____3194 = doc_of_pattern currentModule p  in
                    [uu____3194]  in
                  (FStar_Format.text "|") :: uu____3191  in
                FStar_Format.reduce1 uu____3188
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3198 =
                  let uu____3201 =
                    let uu____3204 = doc_of_pattern currentModule p  in
                    [uu____3204; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____3201  in
                FStar_Format.reduce1 uu____3198
             in
          let uu____3207 =
            let uu____3210 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____3213 =
              let uu____3216 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3216; FStar_Format.text "end"]  in
            uu____3210 :: uu____3213  in
          FStar_Format.combine FStar_Format.hardline uu____3207

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____3219  ->
      match uu____3219 with
      | (rec_,top_level,lets) ->
          let for1 uu____3244 =
            match uu____3244 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3247;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3249;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____3265 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3265
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3268::uu____3269,uu____3270) ->
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
                                let uu____3294 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3294
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____3313 =
                  let uu____3316 =
                    let uu____3319 = FStar_Format.reduce1 ids  in
                    [uu____3319; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____3316  in
                FStar_Format.reduce1 uu____3313
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
  fun uu____3345  ->
    match uu____3345 with
    | (lineno,file) ->
        let uu____3352 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3352
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
      let for1 uu____3404 =
        match uu____3404 with
        | (uu____3427,x,mangle_opt,tparams,uu____3431,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____3466 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____3477 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____3477
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3504 =
                    match uu____3504 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____3517 =
                    let uu____3518 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____3518
                     in
                  FStar_Format.cbrackets uu____3517
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3559 =
                    match uu____3559 with
                    | (name,tys) ->
                        let uu____3590 = FStar_List.split tys  in
                        (match uu____3590 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____3613 ->
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
              let uu____3644 =
                let uu____3647 =
                  let uu____3650 =
                    let uu____3651 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____3651  in
                  [uu____3650]  in
                tparams1 :: uu____3647  in
              FStar_Format.reduce1 uu____3644  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3660 =
                   let uu____3663 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____3663; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____3660)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____3671 =
            let uu____3674 =
              let uu____3677 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____3677]  in
            (FStar_Format.text "type") :: uu____3674  in
          FStar_Format.reduce1 uu____3671
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
          let uu____3713 =
            let uu____3716 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____3719 =
              let uu____3722 = doc_of_sig currentModule subsig  in
              let uu____3723 =
                let uu____3726 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____3726]  in
              uu____3722 :: uu____3723  in
            uu____3716 :: uu____3719  in
          FStar_Format.combine FStar_Format.hardline uu____3713
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3746 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____3746  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3751,ty)) ->
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
            let uu____3830 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____3830  in
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
          let uu____3846 =
            let uu____3849 =
              let uu____3852 =
                let uu____3855 =
                  let uu____3858 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____3858]  in
                (FStar_Format.text "=") :: uu____3855  in
              (FStar_Format.text "_") :: uu____3852  in
            (FStar_Format.text "let") :: uu____3849  in
          FStar_Format.reduce1 uu____3846
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____3888 ->
                  FStar_Format.empty
              | uu____3889 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____3902  ->
    match uu____3902 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3972 =
          match uu____3972 with
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
                  (fun uu____4032  ->
                     match uu____4032 with
                     | (s,uu____4038) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____4059 =
                let uu____4062 = FStar_Format.cat head1 FStar_Format.hardline
                   in
                let uu____4063 =
                  let uu____4066 =
                    match doc1 with
                    | FStar_Pervasives_Native.None  -> FStar_Format.empty
                    | FStar_Pervasives_Native.Some s ->
                        FStar_Format.cat s FStar_Format.hardline
                     in
                  let uu____4068 =
                    let uu____4071 = FStar_Format.reduce sub3  in
                    let uu____4072 =
                      let uu____4075 =
                        FStar_Format.cat tail1 FStar_Format.hardline  in
                      [uu____4075]  in
                    uu____4071 :: uu____4072  in
                  uu____4066 :: uu____4068  in
                uu____4062 :: uu____4063  in
              FStar_Format.reduce uu____4059
        
        and for1_mod istop uu____4077 =
          match uu____4077 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4159 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____4180 =
                  let uu____4183 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4183
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
                FStar_Format.reduce1 uu____4180  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4214  ->
                     match uu____4214 with
                     | (uu____4219,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____4245 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4245
                then
                  let uu____4250 =
                    FStar_Format.cat (FStar_Format.text "#light \"off\"")
                      FStar_Format.hardline
                     in
                  [uu____4250]
                else []  in
              let uu____4254 =
                let uu____4257 =
                  let uu____4260 =
                    let uu____4263 =
                      let uu____4266 =
                        let uu____4269 =
                          match doc1 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Format.empty
                          | FStar_Pervasives_Native.Some s ->
                              FStar_Format.cat s FStar_Format.hardline
                           in
                        let uu____4271 =
                          let uu____4274 = FStar_Format.reduce sub3  in
                          let uu____4275 =
                            let uu____4278 =
                              FStar_Format.cat tail1 FStar_Format.hardline
                               in
                            [uu____4278]  in
                          uu____4274 :: uu____4275  in
                        uu____4269 :: uu____4271  in
                      FStar_Format.hardline :: uu____4266  in
                    FStar_List.append maybe_open_pervasives uu____4263  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____4260
                   in
                FStar_List.append prefix1 uu____4257  in
              FStar_All.pipe_left FStar_Format.reduce uu____4254
         in
        let docs =
          FStar_List.map
            (fun uu____4321  ->
               match uu____4321 with
               | (x,s,m) ->
                   let uu____4378 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4380 = for1_mod true (x, s, m)  in
                   (uu____4378, uu____4380)) mllib
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
        let uu____4423 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4423 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____4439 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4439 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  