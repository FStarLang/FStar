open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | ILeft  -> true | uu____8 -> false 
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____19 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____30 -> false 
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Right  -> true | uu____41 -> false 
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____52 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____68 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____79 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____91 -> false
  
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
    | ([],uu____288) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____312,uu____313) -> false
  
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
                  let uu____394 = FStar_Util.first_N cg_len ns  in
                  match uu____394 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____434 =
                           let uu____438 =
                             let uu____442 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____442]  in
                           FStar_List.append pfx uu____438  in
                         FStar_Pervasives_Native.Some uu____434
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
      let uu____488 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____488 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____504 ->
          let uu____506 = x  in
          (match uu____506 with
           | (ns,x1) ->
               let uu____517 = path_of_ns currentModule ns  in
               (uu____517, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____535 =
      let uu____537 =
        let uu____539 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____539  in
      let uu____542 = FStar_String.get s (Prims.parse_int "0")  in
      uu____537 <> uu____542  in
    if uu____535 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____578 = mlpath_of_mlpath currentModule mlp  in
         match uu____578 with
         | (p,s) ->
             let uu____590 =
               let uu____594 =
                 let uu____598 = ptsym_of_symbol s  in [uu____598]  in
               FStar_List.append p uu____594  in
             FStar_String.concat "." uu____590)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____619 = mlpath_of_mlpath currentModule mlp  in
      match uu____619 with
      | (p,s) ->
          let s1 =
            let uu____633 =
              let uu____635 =
                let uu____637 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____637  in
              let uu____640 = FStar_String.get s (Prims.parse_int "0")  in
              uu____635 <> uu____640  in
            if uu____633 then Prims.op_Hat "U__" s else s  in
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
  fun uu____1003  ->
    let op_minus =
      let uu____1006 =
        let uu____1008 = FStar_Options.codegen ()  in
        uu____1008 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____1006 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____1057 . unit -> 'Auu____1057 Prims.list =
  fun uu____1060  -> [] 
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
  fun uu____1155  ->
    match uu____1155 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1214  ->
               match uu____1214 with | (y,uu____1230,uu____1231) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1269 = as_bin_op p  in
    uu____1269 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1326  ->
    match uu____1326 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____1354 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____1372  ->
               match uu____1372 with | (y,uu____1381) -> x = y) uu____1354
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1402 = as_uni_op p  in
    uu____1402 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1446  ->
    match uu____1446 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1483  ->
               match uu____1483 with | (y,uu____1492) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1513 = as_standard_constructor p  in
    uu____1513 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____1563  ->
    fun inner  ->
      fun doc1  ->
        match uu____1563 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1629 = _inner  in
              match uu____1629 with
              | (pi,fi) ->
                  let uu____1640 = _outer  in
                  (match uu____1640 with
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
                           | (uu____1658,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1660,uu____1661) -> false)))
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
    fun uu___0_1700  ->
      if uu___0_1700 = 92
      then "\\\\"
      else
        if uu___0_1700 = 32
        then " "
        else
          if uu___0_1700 = 8
          then "\\b"
          else
            if uu___0_1700 = 9
            then "\\t"
            else
              if uu___0_1700 = 13
              then "\\r"
              else
                if uu___0_1700 = 10
                then "\\n"
                else
                  if uu___0_1700 = 39
                  then "\\'"
                  else
                    if uu___0_1700 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___0_1700
                      then FStar_Util.string_of_char uu___0_1700
                      else
                        if FStar_Util.is_punctuation uu___0_1700
                        then FStar_Util.string_of_char uu___0_1700
                        else
                          if FStar_Util.is_symbol uu___0_1700
                          then FStar_Util.string_of_char uu___0_1700
                          else fallback uu___0_1700
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1747 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____1747
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
        (s,FStar_Pervasives_Native.Some (uu____1789,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1803,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1835 =
          let uu____1837 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____1837 "\""  in
        Prims.op_Hat "\"" uu____1835
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1843 =
          let uu____1845 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____1845 "\""  in
        Prims.op_Hat "\"" uu____1843
    | uu____1849 ->
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
              let uu____1908 =
                let uu____1909 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____1909  in
              FStar_Format.parens uu____1908  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1919 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____1925 =
                    let uu____1926 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____1926  in
                  FStar_Format.parens uu____1925
               in
            let name1 = ptsym currentModule name  in
            let uu____1930 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____1930
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1932,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____1936 =
              let uu____1937 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____1937  in
            maybe_paren outer t_prio_fun uu____1936
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1939 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1939
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
        let uu____1951 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____1951

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
            let uu____2044 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2044
            then
              let uu____2047 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____2047
            else
              (let uu____2051 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____2051)
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
            let uu____2065 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____2065
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2067 = string_of_mlconstant c  in
            FStar_Format.text uu____2067
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2072 = ptsym currentModule path  in
            FStar_Format.text uu____2072
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2106 =
              match uu____2106 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2117 =
                    let uu____2120 =
                      let uu____2121 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____2121  in
                    [uu____2120; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____2117
               in
            let uu____2128 =
              let uu____2129 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____2129  in
            FStar_Format.cbrackets uu____2128
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2143 = is_standard_constructor ctor  in
              if uu____2143
              then
                let uu____2147 =
                  let uu____2154 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2154  in
                FStar_Pervasives_Native.snd uu____2147
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2181 = is_standard_constructor ctor  in
              if uu____2181
              then
                let uu____2185 =
                  let uu____2192 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2192  in
                FStar_Pervasives_Native.snd uu____2185
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
              | (uu____2225,uu____2226) ->
                  let uu____2233 =
                    let uu____2236 =
                      let uu____2239 =
                        let uu____2240 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____2240  in
                      [uu____2239]  in
                    (FStar_Format.text name) :: uu____2236  in
                  FStar_Format.reduce1 uu____2233
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2251 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____2251) es
               in
            let docs1 =
              let uu____2253 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____2253  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2270 =
                  let uu____2273 =
                    let uu____2276 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2276]  in
                  FStar_Format.hardline :: uu____2273  in
                FStar_Format.reduce uu____2270
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2285 =
              let uu____2286 =
                let uu____2289 =
                  let uu____2292 =
                    let uu____2295 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____2295]  in
                  doc1 :: uu____2292  in
                pre :: uu____2289  in
              FStar_Format.combine FStar_Format.hardline uu____2286  in
            FStar_Format.parens uu____2285
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2306::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2308;
                    FStar_Extraction_ML_Syntax.loc = uu____2309;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2311)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2313;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2314;_}::[])
                 when
                 let uu____2358 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2358 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2384;
                            FStar_Extraction_ML_Syntax.loc = uu____2385;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2387;
                       FStar_Extraction_ML_Syntax.loc = uu____2388;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2446;
                   FStar_Extraction_ML_Syntax.loc = uu____2447;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2460;
                   FStar_Extraction_ML_Syntax.loc = uu____2461;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2468 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2479 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____2479)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____2484 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2484
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2494 =
                   let uu____2497 =
                     let uu____2500 =
                       let uu____2503 =
                         let uu____2504 = ptsym currentModule f  in
                         FStar_Format.text uu____2504  in
                       [uu____2503]  in
                     (FStar_Format.text ".") :: uu____2500  in
                   e2 :: uu____2497  in
                 FStar_Format.reduce uu____2494)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2540 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2540
              then
                let uu____2543 =
                  let uu____2546 =
                    let uu____2549 =
                      let uu____2552 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2554 =
                              let uu____2557 =
                                let uu____2560 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2560]  in
                              (FStar_Format.text " : ") :: uu____2557  in
                            FStar_Format.reduce1 uu____2554
                        | uu____2562 -> FStar_Format.text ""  in
                      [uu____2552; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____2549  in
                  (FStar_Format.text "(") :: uu____2546  in
                FStar_Format.reduce1 uu____2543
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2581  ->
                   match uu____2581 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____2593 =
                let uu____2596 =
                  let uu____2599 = FStar_Format.reduce1 ids1  in
                  [uu____2599; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____2596  in
              FStar_Format.reduce1 uu____2593  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2608 =
                let uu____2611 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____2615 =
                  let uu____2618 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2618; FStar_Format.text "end"]  in
                uu____2611 :: uu____2615  in
              FStar_Format.combine FStar_Format.hardline uu____2608  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2627 =
                let uu____2630 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____2634 =
                  let uu____2637 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2638 =
                    let uu____2641 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____2645 =
                      let uu____2648 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2648; FStar_Format.text "end"]  in
                    uu____2641 :: uu____2645  in
                  uu____2637 :: uu____2638  in
                uu____2630 :: uu____2634  in
              FStar_Format.combine FStar_Format.hardline uu____2627  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2687 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____2687 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2694 =
              let uu____2697 =
                let uu____2700 =
                  let uu____2701 = ptctor currentModule exn  in
                  FStar_Format.text uu____2701  in
                [uu____2700]  in
              (FStar_Format.text "raise") :: uu____2697  in
            FStar_Format.reduce1 uu____2694
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2713 =
              let uu____2716 =
                let uu____2719 =
                  let uu____2720 = ptctor currentModule exn  in
                  FStar_Format.text uu____2720  in
                let uu____2722 =
                  let uu____2725 =
                    let uu____2726 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____2726  in
                  [uu____2725]  in
                uu____2719 :: uu____2722  in
              (FStar_Format.text "raise") :: uu____2716  in
            FStar_Format.reduce1 uu____2713
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2751 =
              let uu____2754 =
                let uu____2757 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2758 =
                  let uu____2761 =
                    let uu____2764 =
                      let uu____2765 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____2765
                       in
                    [uu____2764]  in
                  (FStar_Format.text "with") :: uu____2761  in
                uu____2757 :: uu____2758  in
              (FStar_Format.text "try") :: uu____2754  in
            FStar_Format.combine FStar_Format.hardline uu____2751
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
          let uu____2789 =
            let uu____2803 = as_bin_op p  in FStar_Option.get uu____2803  in
          match uu____2789 with
          | (uu____2832,prio,txt) ->
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
        let uu____2856 =
          let uu____2863 = as_uni_op p  in FStar_Option.get uu____2863  in
        match uu____2856 with
        | (uu____2878,txt) ->
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
          let uu____2891 = string_of_mlconstant c  in
          FStar_Format.text uu____2891
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2927 =
            match uu____2927 with
            | (name,p) ->
                let uu____2937 =
                  let uu____2940 =
                    let uu____2941 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2941  in
                  let uu____2947 =
                    let uu____2950 =
                      let uu____2953 = doc_of_pattern currentModule p  in
                      [uu____2953]  in
                    (FStar_Format.text "=") :: uu____2950  in
                  uu____2940 :: uu____2947  in
                FStar_Format.reduce1 uu____2937
             in
          let uu____2955 =
            let uu____2956 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____2956  in
          FStar_Format.cbrackets uu____2955
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2970 = is_standard_constructor ctor  in
            if uu____2970
            then
              let uu____2974 =
                let uu____2981 = as_standard_constructor ctor  in
                FStar_Option.get uu____2981  in
              FStar_Pervasives_Native.snd uu____2974
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3008 = is_standard_constructor ctor  in
            if uu____3008
            then
              let uu____3012 =
                let uu____3019 = as_standard_constructor ctor  in
                FStar_Option.get uu____3019  in
              FStar_Pervasives_Native.snd uu____3012
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3048 =
                  let uu____3051 =
                    let uu____3052 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____3052  in
                  let uu____3053 =
                    let uu____3056 =
                      let uu____3059 = doc_of_pattern currentModule xs  in
                      [uu____3059]  in
                    (FStar_Format.text "::") :: uu____3056  in
                  uu____3051 :: uu____3053  in
                FStar_Format.reduce uu____3048
            | (uu____3061,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3062)::[]) ->
                let uu____3069 =
                  let uu____3072 =
                    let uu____3075 =
                      let uu____3076 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3076  in
                    [uu____3075]  in
                  (FStar_Format.text name) :: uu____3072  in
                FStar_Format.reduce1 uu____3069
            | uu____3077 ->
                let uu____3085 =
                  let uu____3088 =
                    let uu____3091 =
                      let uu____3092 =
                        let uu____3093 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____3093
                         in
                      FStar_Format.parens uu____3092  in
                    [uu____3091]  in
                  (FStar_Format.text name) :: uu____3088  in
                FStar_Format.reduce1 uu____3085
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3108 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____3108
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____3121  ->
      match uu____3121 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3131 =
                  let uu____3134 =
                    let uu____3137 = doc_of_pattern currentModule p  in
                    [uu____3137]  in
                  (FStar_Format.text "|") :: uu____3134  in
                FStar_Format.reduce1 uu____3131
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3141 =
                  let uu____3144 =
                    let uu____3147 = doc_of_pattern currentModule p  in
                    [uu____3147; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____3144  in
                FStar_Format.reduce1 uu____3141
             in
          let uu____3150 =
            let uu____3153 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____3156 =
              let uu____3159 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3159; FStar_Format.text "end"]  in
            uu____3153 :: uu____3156  in
          FStar_Format.combine FStar_Format.hardline uu____3150

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____3162  ->
      match uu____3162 with
      | (rec_,top_level,lets) ->
          let for1 uu____3187 =
            match uu____3187 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3190;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3192;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____3208 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3208
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3211::uu____3212,uu____3213) ->
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
                                let uu____3237 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3237
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____3256 =
                  let uu____3259 =
                    let uu____3262 = FStar_Format.reduce1 ids  in
                    [uu____3262; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____3259  in
                FStar_Format.reduce1 uu____3256
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
  fun uu____3288  ->
    match uu____3288 with
    | (lineno,file) ->
        let uu____3295 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3295
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
      let for1 uu____3347 =
        match uu____3347 with
        | (uu____3370,x,mangle_opt,tparams,uu____3374,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____3409 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____3420 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____3420
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3447 =
                    match uu____3447 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____3460 =
                    let uu____3461 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____3461
                     in
                  FStar_Format.cbrackets uu____3460
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3502 =
                    match uu____3502 with
                    | (name,tys) ->
                        let uu____3533 = FStar_List.split tys  in
                        (match uu____3533 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____3556 ->
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
              let uu____3587 =
                let uu____3590 =
                  let uu____3593 =
                    let uu____3594 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____3594  in
                  [uu____3593]  in
                tparams1 :: uu____3590  in
              FStar_Format.reduce1 uu____3587  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3603 =
                   let uu____3606 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____3606; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____3603)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____3614 =
            let uu____3617 =
              let uu____3620 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____3620]  in
            (FStar_Format.text "type") :: uu____3617  in
          FStar_Format.reduce1 uu____3614
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
          let uu____3656 =
            let uu____3659 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____3662 =
              let uu____3665 = doc_of_sig currentModule subsig  in
              let uu____3666 =
                let uu____3669 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____3669]  in
              uu____3665 :: uu____3666  in
            uu____3659 :: uu____3662  in
          FStar_Format.combine FStar_Format.hardline uu____3656
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3689 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____3689  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3694,ty)) ->
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
            let uu____3773 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____3773  in
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
          let uu____3789 =
            let uu____3792 =
              let uu____3795 =
                let uu____3798 =
                  let uu____3801 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____3801]  in
                (FStar_Format.text "=") :: uu____3798  in
              (FStar_Format.text "_") :: uu____3795  in
            (FStar_Format.text "let") :: uu____3792  in
          FStar_Format.reduce1 uu____3789
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____3831 ->
                  FStar_Format.empty
              | uu____3832 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____3845  ->
    match uu____3845 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3915 =
          match uu____3915 with
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
                  (fun uu____3975  ->
                     match uu____3975 with
                     | (s,uu____3981) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____4002 =
                let uu____4005 =
                  let uu____4008 =
                    let uu____4011 = FStar_Format.reduce sub3  in
                    [uu____4011;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____4008
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____4005
                 in
              FStar_Format.reduce uu____4002
        
        and for1_mod istop uu____4014 =
          match uu____4014 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4096 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____4117 =
                  let uu____4120 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4120
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
                FStar_Format.reduce1 uu____4117  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4151  ->
                     match uu____4151 with
                     | (uu____4156,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____4182 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4182
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____4190 =
                let uu____4193 =
                  let uu____4196 =
                    let uu____4199 =
                      let uu____4202 =
                        let uu____4205 =
                          let uu____4208 = FStar_Format.reduce sub3  in
                          [uu____4208;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____4205
                         in
                      FStar_Format.hardline :: uu____4202  in
                    FStar_List.append maybe_open_pervasives uu____4199  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____4196
                   in
                FStar_List.append prefix1 uu____4193  in
              FStar_All.pipe_left FStar_Format.reduce uu____4190
         in
        let docs =
          FStar_List.map
            (fun uu____4252  ->
               match uu____4252 with
               | (x,s,m) ->
                   let uu____4309 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4311 = for1_mod true (x, s, m)  in
                   (uu____4309, uu____4311)) mllib
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
        let uu____4354 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4354 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____4370 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4370 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  