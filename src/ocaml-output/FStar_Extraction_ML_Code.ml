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
    if uu____545 then Prims.strcat "l__" s else s
  
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
            if uu____643 then Prims.strcat "U__" s else s  in
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
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___272_1710  ->
      if uu___272_1710 = 92
      then "\\\\"
      else
        if uu___272_1710 = 32
        then " "
        else
          if uu___272_1710 = 8
          then "\\b"
          else
            if uu___272_1710 = 9
            then "\\t"
            else
              if uu___272_1710 = 13
              then "\\r"
              else
                if uu___272_1710 = 10
                then "\\n"
                else
                  if uu___272_1710 = 39
                  then "\\'"
                  else
                    if uu___272_1710 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___272_1710
                      then FStar_Util.string_of_char uu___272_1710
                      else
                        if FStar_Util.is_punctuation uu___272_1710
                        then FStar_Util.string_of_char uu___272_1710
                        else
                          if FStar_Util.is_symbol uu___272_1710
                          then FStar_Util.string_of_char uu___272_1710
                          else fallback uu___272_1710
  
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
        Prims.strcat uu____1757
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
        (s,FStar_Pervasives_Native.Some (uu____1821,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1835,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1867 =
          let uu____1869 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat uu____1869 "\""  in
        Prims.strcat "\"" uu____1867
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1875 =
          let uu____1877 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat uu____1877 "\""  in
        Prims.strcat "\"" uu____1875
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
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
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
            let uu____2097 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____2097
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2099 = string_of_mlconstant c  in
            FStar_Format.text uu____2099
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2104 = ptsym currentModule path  in
            FStar_Format.text uu____2104
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2138 =
              match uu____2138 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2149 =
                    let uu____2152 =
                      let uu____2153 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____2153  in
                    [uu____2152; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____2149
               in
            let uu____2160 =
              let uu____2161 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____2161  in
            FStar_Format.cbrackets uu____2160
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2175 = is_standard_constructor ctor  in
              if uu____2175
              then
                let uu____2179 =
                  let uu____2186 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2186  in
                FStar_Pervasives_Native.snd uu____2179
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2213 = is_standard_constructor ctor  in
              if uu____2213
              then
                let uu____2217 =
                  let uu____2224 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2224  in
                FStar_Pervasives_Native.snd uu____2217
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
              | (uu____2257,uu____2258) ->
                  let uu____2265 =
                    let uu____2268 =
                      let uu____2271 =
                        let uu____2272 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____2272  in
                      [uu____2271]  in
                    (FStar_Format.text name) :: uu____2268  in
                  FStar_Format.reduce1 uu____2265
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2283 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____2283) es
               in
            let docs1 =
              let uu____2285 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____2285  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2302 =
                  let uu____2305 =
                    let uu____2308 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2308]  in
                  FStar_Format.hardline :: uu____2305  in
                FStar_Format.reduce uu____2302
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2317 =
              let uu____2318 =
                let uu____2321 =
                  let uu____2324 =
                    let uu____2327 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____2327]  in
                  doc1 :: uu____2324  in
                pre :: uu____2321  in
              FStar_Format.combine FStar_Format.hardline uu____2318  in
            FStar_Format.parens uu____2317
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2338::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2340;
                    FStar_Extraction_ML_Syntax.loc = uu____2341;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2343)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2345;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2346;_}::[])
                 when
                 let uu____2390 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2390 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2416;
                            FStar_Extraction_ML_Syntax.loc = uu____2417;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2419;
                       FStar_Extraction_ML_Syntax.loc = uu____2420;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2478;
                   FStar_Extraction_ML_Syntax.loc = uu____2479;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2492;
                   FStar_Extraction_ML_Syntax.loc = uu____2493;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2500 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2511 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____2511)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____2516 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2516
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2526 =
                   let uu____2529 =
                     let uu____2532 =
                       let uu____2535 =
                         let uu____2536 = ptsym currentModule f  in
                         FStar_Format.text uu____2536  in
                       [uu____2535]  in
                     (FStar_Format.text ".") :: uu____2532  in
                   e2 :: uu____2529  in
                 FStar_Format.reduce uu____2526)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2572 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2572
              then
                let uu____2575 =
                  let uu____2578 =
                    let uu____2581 =
                      let uu____2584 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2586 =
                              let uu____2589 =
                                let uu____2592 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2592]  in
                              (FStar_Format.text " : ") :: uu____2589  in
                            FStar_Format.reduce1 uu____2586
                        | uu____2594 -> FStar_Format.text ""  in
                      [uu____2584; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____2581  in
                  (FStar_Format.text "(") :: uu____2578  in
                FStar_Format.reduce1 uu____2575
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2613  ->
                   match uu____2613 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____2625 =
                let uu____2628 =
                  let uu____2631 = FStar_Format.reduce1 ids1  in
                  [uu____2631; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____2628  in
              FStar_Format.reduce1 uu____2625  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2640 =
                let uu____2643 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____2647 =
                  let uu____2650 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2650; FStar_Format.text "end"]  in
                uu____2643 :: uu____2647  in
              FStar_Format.combine FStar_Format.hardline uu____2640  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2659 =
                let uu____2662 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____2666 =
                  let uu____2669 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2670 =
                    let uu____2673 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____2677 =
                      let uu____2680 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2680; FStar_Format.text "end"]  in
                    uu____2673 :: uu____2677  in
                  uu____2669 :: uu____2670  in
                uu____2662 :: uu____2666  in
              FStar_Format.combine FStar_Format.hardline uu____2659  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2719 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____2719 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2726 =
              let uu____2729 =
                let uu____2732 =
                  let uu____2733 = ptctor currentModule exn  in
                  FStar_Format.text uu____2733  in
                [uu____2732]  in
              (FStar_Format.text "raise") :: uu____2729  in
            FStar_Format.reduce1 uu____2726
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2745 =
              let uu____2748 =
                let uu____2751 =
                  let uu____2752 = ptctor currentModule exn  in
                  FStar_Format.text uu____2752  in
                let uu____2754 =
                  let uu____2757 =
                    let uu____2758 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____2758  in
                  [uu____2757]  in
                uu____2751 :: uu____2754  in
              (FStar_Format.text "raise") :: uu____2748  in
            FStar_Format.reduce1 uu____2745
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2783 =
              let uu____2786 =
                let uu____2789 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2790 =
                  let uu____2793 =
                    let uu____2796 =
                      let uu____2797 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____2797
                       in
                    [uu____2796]  in
                  (FStar_Format.text "with") :: uu____2793  in
                uu____2789 :: uu____2790  in
              (FStar_Format.text "try") :: uu____2786  in
            FStar_Format.combine FStar_Format.hardline uu____2783
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
          let uu____2821 =
            let uu____2835 = as_bin_op p  in FStar_Option.get uu____2835  in
          match uu____2821 with
          | (uu____2864,prio,txt) ->
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
        let uu____2888 =
          let uu____2895 = as_uni_op p  in FStar_Option.get uu____2895  in
        match uu____2888 with
        | (uu____2910,txt) ->
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
          let uu____2923 = string_of_mlconstant c  in
          FStar_Format.text uu____2923
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2959 =
            match uu____2959 with
            | (name,p) ->
                let uu____2969 =
                  let uu____2972 =
                    let uu____2973 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2973  in
                  let uu____2979 =
                    let uu____2982 =
                      let uu____2985 = doc_of_pattern currentModule p  in
                      [uu____2985]  in
                    (FStar_Format.text "=") :: uu____2982  in
                  uu____2972 :: uu____2979  in
                FStar_Format.reduce1 uu____2969
             in
          let uu____2987 =
            let uu____2988 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____2988  in
          FStar_Format.cbrackets uu____2987
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____3002 = is_standard_constructor ctor  in
            if uu____3002
            then
              let uu____3006 =
                let uu____3013 = as_standard_constructor ctor  in
                FStar_Option.get uu____3013  in
              FStar_Pervasives_Native.snd uu____3006
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3040 = is_standard_constructor ctor  in
            if uu____3040
            then
              let uu____3044 =
                let uu____3051 = as_standard_constructor ctor  in
                FStar_Option.get uu____3051  in
              FStar_Pervasives_Native.snd uu____3044
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3080 =
                  let uu____3083 =
                    let uu____3084 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____3084  in
                  let uu____3085 =
                    let uu____3088 =
                      let uu____3091 = doc_of_pattern currentModule xs  in
                      [uu____3091]  in
                    (FStar_Format.text "::") :: uu____3088  in
                  uu____3083 :: uu____3085  in
                FStar_Format.reduce uu____3080
            | (uu____3093,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3094)::[]) ->
                let uu____3101 =
                  let uu____3104 =
                    let uu____3107 =
                      let uu____3108 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3108  in
                    [uu____3107]  in
                  (FStar_Format.text name) :: uu____3104  in
                FStar_Format.reduce1 uu____3101
            | uu____3109 ->
                let uu____3117 =
                  let uu____3120 =
                    let uu____3123 =
                      let uu____3124 =
                        let uu____3125 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____3125
                         in
                      FStar_Format.parens uu____3124  in
                    [uu____3123]  in
                  (FStar_Format.text name) :: uu____3120  in
                FStar_Format.reduce1 uu____3117
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3140 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____3140
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____3153  ->
      match uu____3153 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3163 =
                  let uu____3166 =
                    let uu____3169 = doc_of_pattern currentModule p  in
                    [uu____3169]  in
                  (FStar_Format.text "|") :: uu____3166  in
                FStar_Format.reduce1 uu____3163
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3173 =
                  let uu____3176 =
                    let uu____3179 = doc_of_pattern currentModule p  in
                    [uu____3179; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____3176  in
                FStar_Format.reduce1 uu____3173
             in
          let uu____3182 =
            let uu____3185 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____3188 =
              let uu____3191 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3191; FStar_Format.text "end"]  in
            uu____3185 :: uu____3188  in
          FStar_Format.combine FStar_Format.hardline uu____3182

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____3194  ->
      match uu____3194 with
      | (rec_,top_level,lets) ->
          let for1 uu____3219 =
            match uu____3219 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3222;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3224;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____3240 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3240
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3243::uu____3244,uu____3245) ->
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
                                let uu____3269 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3269
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____3288 =
                  let uu____3291 =
                    let uu____3294 = FStar_Format.reduce1 ids  in
                    [uu____3294; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____3291  in
                FStar_Format.reduce1 uu____3288
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
  fun uu____3320  ->
    match uu____3320 with
    | (lineno,file) ->
        let uu____3327 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3327
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
      let for1 uu____3379 =
        match uu____3379 with
        | (uu____3402,x,mangle_opt,tparams,uu____3406,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____3441 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____3452 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____3452
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3479 =
                    match uu____3479 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____3492 =
                    let uu____3493 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____3493
                     in
                  FStar_Format.cbrackets uu____3492
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3534 =
                    match uu____3534 with
                    | (name,tys) ->
                        let uu____3565 = FStar_List.split tys  in
                        (match uu____3565 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____3588 ->
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
              let uu____3619 =
                let uu____3622 =
                  let uu____3625 =
                    let uu____3626 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____3626  in
                  [uu____3625]  in
                tparams1 :: uu____3622  in
              FStar_Format.reduce1 uu____3619  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3635 =
                   let uu____3638 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____3638; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____3635)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____3646 =
            let uu____3649 =
              let uu____3652 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____3652]  in
            (FStar_Format.text "type") :: uu____3649  in
          FStar_Format.reduce1 uu____3646
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
          let uu____3688 =
            let uu____3691 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____3694 =
              let uu____3697 = doc_of_sig currentModule subsig  in
              let uu____3698 =
                let uu____3701 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____3701]  in
              uu____3697 :: uu____3698  in
            uu____3691 :: uu____3694  in
          FStar_Format.combine FStar_Format.hardline uu____3688
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3721 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____3721  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3726,ty)) ->
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
            let uu____3805 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____3805  in
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
          let uu____3821 =
            let uu____3824 =
              let uu____3827 =
                let uu____3830 =
                  let uu____3833 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____3833]  in
                (FStar_Format.text "=") :: uu____3830  in
              (FStar_Format.text "_") :: uu____3827  in
            (FStar_Format.text "let") :: uu____3824  in
          FStar_Format.reduce1 uu____3821
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____3863 ->
                  FStar_Format.empty
              | uu____3864 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____3877  ->
    match uu____3877 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3947 =
          match uu____3947 with
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
                  (fun uu____4007  ->
                     match uu____4007 with
                     | (s,uu____4013) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____4034 =
                let uu____4037 =
                  let uu____4040 =
                    let uu____4043 = FStar_Format.reduce sub3  in
                    [uu____4043;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____4040
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____4037
                 in
              FStar_Format.reduce uu____4034
        
        and for1_mod istop uu____4046 =
          match uu____4046 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4128 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)]
                 in
              let head1 =
                let uu____4149 =
                  let uu____4152 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4152
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
                FStar_Format.reduce1 uu____4149  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4183  ->
                     match uu____4183 with
                     | (uu____4188,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____4214 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4214
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____4222 =
                let uu____4225 =
                  let uu____4228 =
                    let uu____4231 =
                      let uu____4234 =
                        let uu____4237 =
                          let uu____4240 = FStar_Format.reduce sub3  in
                          [uu____4240;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____4237
                         in
                      FStar_Format.hardline :: uu____4234  in
                    FStar_List.append maybe_open_pervasives uu____4231  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____4228
                   in
                FStar_List.append prefix1 uu____4225  in
              FStar_All.pipe_left FStar_Format.reduce uu____4222
         in
        let docs =
          FStar_List.map
            (fun uu____4284  ->
               match uu____4284 with
               | (x,s,m) ->
                   let uu____4341 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4343 = for1_mod true (x, s, m)  in
                   (uu____4341, uu____4343)) mllib
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
        let uu____4386 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4386 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____4402 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4402 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  