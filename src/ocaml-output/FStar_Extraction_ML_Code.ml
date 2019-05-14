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
type doc =
  | Doc of Prims.string 
let (uu___is_Doc : doc -> Prims.bool) = fun projectee  -> true 
let (__proj__Doc__item___0 : doc -> Prims.string) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
let (empty : doc) = Doc "" 
let (hardline : doc) = Doc "\n" 
let (text : Prims.string -> doc) = fun s  -> Doc s 
let (num : Prims.int -> doc) =
  fun i  -> let uu____320 = FStar_Util.string_of_int i  in Doc uu____320 
let (break1 : doc) = text " " 
let (enclose : doc -> doc -> doc -> doc) =
  fun uu____345  ->
    fun uu____346  ->
      fun uu____347  ->
        match (uu____345, uu____346, uu____347) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.op_Hat l (Prims.op_Hat x r))
  
let (cbrackets : doc -> doc) =
  fun uu____373  ->
    match uu____373 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____389  ->
    match uu____389 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____410  ->
    fun uu____411  ->
      match (uu____410, uu____411) with
      | (Doc d1,Doc d2) -> Doc (Prims.op_Hat d1 d2)
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____452  ->
    fun docs  ->
      match uu____452 with
      | Doc sep ->
          let select uu____470 =
            match uu____470 with
            | Doc d ->
                if d = ""
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some d
             in
          let docs1 = FStar_List.choose select docs  in
          Doc (FStar_String.concat sep docs1)
  
let (reduce1 : doc Prims.list -> doc) = fun docs  -> combine break1 docs 
let (hbox : doc -> doc) = fun d  -> d 
let rec in_ns : 'a . ('a Prims.list * 'a Prims.list) -> Prims.bool =
  fun x  ->
    match x with
    | ([],uu____545) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____569,uu____570) -> false
  
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
                  let uu____651 = FStar_Util.first_N cg_len ns  in
                  match uu____651 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____691 =
                           let uu____695 =
                             let uu____699 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____699]  in
                           FStar_List.append pfx uu____695  in
                         FStar_Pervasives_Native.Some uu____691
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
      let uu____745 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____745 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____761 ->
          let uu____763 = x  in
          (match uu____763 with
           | (ns,x1) ->
               let uu____774 = path_of_ns currentModule ns  in
               (uu____774, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____792 =
      let uu____794 =
        let uu____796 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____796  in
      let uu____799 = FStar_String.get s (Prims.parse_int "0")  in
      uu____794 <> uu____799  in
    if uu____792 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____835 = mlpath_of_mlpath currentModule mlp  in
         match uu____835 with
         | (p,s) ->
             let uu____847 =
               let uu____851 =
                 let uu____855 = ptsym_of_symbol s  in [uu____855]  in
               FStar_List.append p uu____851  in
             FStar_String.concat "." uu____847)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____876 = mlpath_of_mlpath currentModule mlp  in
      match uu____876 with
      | (p,s) ->
          let s1 =
            let uu____890 =
              let uu____892 =
                let uu____894 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____894  in
              let uu____897 = FStar_String.get s (Prims.parse_int "0")  in
              uu____892 <> uu____897  in
            if uu____890 then Prims.op_Hat "U__" s else s  in
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
  fun uu____1260  ->
    let op_minus =
      let uu____1263 =
        let uu____1265 = FStar_Options.codegen ()  in
        uu____1265 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____1263 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____1314 . unit -> 'Auu____1314 Prims.list =
  fun uu____1317  -> [] 
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
  fun uu____1412  ->
    match uu____1412 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1471  ->
               match uu____1471 with | (y,uu____1487,uu____1488) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1526 = as_bin_op p  in
    uu____1526 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1583  ->
    match uu____1583 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____1611 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____1629  ->
               match uu____1629 with | (y,uu____1638) -> x = y) uu____1611
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1659 = as_uni_op p  in
    uu____1659 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1703  ->
    match uu____1703 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1740  ->
               match uu____1740 with | (y,uu____1749) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1770 = as_standard_constructor p  in
    uu____1770 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) -> (Prims.int * fixity) -> doc -> doc) =
  fun uu____1824  ->
    fun inner  ->
      fun doc1  ->
        match uu____1824 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1892 = _inner  in
              match uu____1892 with
              | (pi,fi) ->
                  let uu____1903 = _outer  in
                  (match uu____1903 with
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
                           | (uu____1921,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1923,uu____1924) -> false)))
               in
            if noparens inner outer side then doc1 else parens doc1
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___0_1964  ->
      if uu___0_1964 = 92
      then "\\\\"
      else
        if uu___0_1964 = 32
        then " "
        else
          if uu___0_1964 = 8
          then "\\b"
          else
            if uu___0_1964 = 9
            then "\\t"
            else
              if uu___0_1964 = 13
              then "\\r"
              else
                if uu___0_1964 = 10
                then "\\n"
                else
                  if uu___0_1964 = 39
                  then "\\'"
                  else
                    if uu___0_1964 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___0_1964
                      then FStar_Util.string_of_char uu___0_1964
                      else
                        if FStar_Util.is_punctuation uu___0_1964
                        then FStar_Util.string_of_char uu___0_1964
                        else
                          if FStar_Util.is_symbol uu___0_1964
                          then FStar_Util.string_of_char uu___0_1964
                          else fallback uu___0_1964
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____2011 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____2011
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
        (s,FStar_Pervasives_Native.Some (uu____2053,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____2067,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____2099 =
          let uu____2101 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____2101 "\""  in
        Prims.op_Hat "\"" uu____2099
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____2107 =
          let uu____2109 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____2109 "\""  in
        Prims.op_Hat "\"" uu____2107
    | uu____2113 ->
        failwith "TODO: extract integer constants properly into OCaml"
  
let rec (doc_of_mltype' :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
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
            text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc2 =
              let uu____2179 =
                let uu____2182 = combine (text " * ") doc1  in
                hbox uu____2182  in
              parens uu____2179  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____2197 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____2205 =
                    let uu____2208 = combine (text ", ") args1  in
                    hbox uu____2208  in
                  parens uu____2205
               in
            let name1 = ptsym currentModule name  in
            let uu____2214 = reduce1 [args1; text name1]  in hbox uu____2214
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2221,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____2229 =
              let uu____2232 = reduce1 [d1; text " -> "; d2]  in
              hbox uu____2232  in
            maybe_paren outer t_prio_fun uu____2229
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____2240 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2240 then text "obj" else text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____2253 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____2253

let rec (doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____2383 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2383
            then
              let uu____2387 = reduce [text "Prims.unsafe_coerce "; doc1]  in
              parens uu____2387
            else
              (let uu____2396 = reduce [text "Obj.magic "; parens doc1]  in
               parens uu____2396)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map (fun d  -> reduce [d; text ";"; hardline]) docs
               in
            let uu____2431 = reduce docs1  in parens uu____2431
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2435 = string_of_mlconstant c  in text uu____2435
        | FStar_Extraction_ML_Syntax.MLE_Var x -> text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2440 = ptsym currentModule path  in text uu____2440
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2484 =
              match uu____2484 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2507 =
                    let uu____2511 =
                      let uu____2514 = ptsym currentModule (path, name)  in
                      text uu____2514  in
                    [uu____2511; text "="; doc1]  in
                  reduce1 uu____2507
               in
            let uu____2525 =
              let uu____2528 = FStar_List.map for1 fields  in
              combine (text "; ") uu____2528  in
            cbrackets uu____2525
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2553 = is_standard_constructor ctor  in
              if uu____2553
              then
                let uu____2557 =
                  let uu____2564 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2564  in
                FStar_Pervasives_Native.snd uu____2557
              else ptctor currentModule ctor  in
            text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2597 = is_standard_constructor ctor  in
              if uu____2597
              then
                let uu____2601 =
                  let uu____2608 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2608  in
                FStar_Pervasives_Native.snd uu____2601
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) -> reduce [parens x; text "::"; xs]
              | (uu____2660,uu____2661) ->
                  let uu____2670 =
                    let uu____2674 =
                      let uu____2678 =
                        let uu____2681 = combine (text ", ") args1  in
                        parens uu____2681  in
                      [uu____2678]  in
                    (text name) :: uu____2674  in
                  reduce1 uu____2670
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2708 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   parens uu____2708) es
               in
            let docs1 =
              let uu____2714 = combine (text ", ") docs  in parens uu____2714
               in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2760 =
                  let uu____2764 =
                    let uu____2768 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2768]  in
                  hardline :: uu____2764  in
                reduce uu____2760
              else empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2792 =
              let uu____2795 =
                let uu____2799 =
                  let uu____2803 =
                    let uu____2807 = reduce1 [text "in"; body1]  in
                    [uu____2807]  in
                  doc1 :: uu____2803  in
                pre :: uu____2799  in
              combine hardline uu____2795  in
            parens uu____2792
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2843::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2845;
                    FStar_Extraction_ML_Syntax.loc = uu____2846;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2848)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2850;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2851;_}::[])
                 when
                 let uu____2919 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2919 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2957;
                            FStar_Extraction_ML_Syntax.loc = uu____2958;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2960;
                       FStar_Extraction_ML_Syntax.loc = uu____2961;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____3085;
                   FStar_Extraction_ML_Syntax.loc = uu____3086;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____3147;
                   FStar_Extraction_ML_Syntax.loc = uu____3148;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____3185 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____3206 = reduce1 (e2 :: args1)  in parens uu____3206)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____3224 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____3224
              then
                reduce [e2; text "."; text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____3239 =
                   let uu____3243 =
                     let uu____3247 =
                       let uu____3251 =
                         let uu____3254 = ptsym currentModule f  in
                         text uu____3254  in
                       [uu____3251]  in
                     (text ".") :: uu____3247  in
                   e2 :: uu____3243  in
                 reduce uu____3239)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____3301 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____3301
              then
                let uu____3305 =
                  let uu____3309 =
                    let uu____3313 =
                      let uu____3317 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____3322 =
                              let uu____3326 =
                                let uu____3330 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____3330]  in
                              (text " : ") :: uu____3326  in
                            reduce1 uu____3322
                        | uu____3337 -> text ""  in
                      [uu____3317; text ")"]  in
                    (text x) :: uu____3313  in
                  (text "(") :: uu____3309  in
                reduce1 uu____3305
              else text x  in
            let ids1 =
              FStar_List.map
                (fun uu____3363  ->
                   match uu____3363 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____3380 =
                let uu____3384 =
                  let uu____3388 = reduce1 ids1  in
                  [uu____3388; text "->"; body1]  in
                (text "fun") :: uu____3384  in
              reduce1 uu____3380  in
            parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____3426 =
                let uu____3430 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____3441 =
                  let uu____3445 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____3445; text "end"]  in
                uu____3430 :: uu____3441  in
              combine hardline uu____3426  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____3485 =
                let uu____3489 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____3500 =
                  let uu____3504 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____3507 =
                    let uu____3511 =
                      reduce1 [text "end"; text "else"; text "begin"]  in
                    let uu____3521 =
                      let uu____3525 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____3525; text "end"]  in
                    uu____3511 :: uu____3521  in
                  uu____3504 :: uu____3507  in
                uu____3489 :: uu____3500  in
              combine hardline uu____3485  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____3601 =
                reduce1 [text "match"; parens cond1; text "with"]  in
              uu____3601 :: pats1  in
            let doc2 = combine hardline doc1  in parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____3623 =
              let uu____3627 =
                let uu____3631 =
                  let uu____3634 = ptctor currentModule exn  in
                  text uu____3634  in
                [uu____3631]  in
              (text "raise") :: uu____3627  in
            reduce1 uu____3623
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____3660 =
              let uu____3664 =
                let uu____3668 =
                  let uu____3671 = ptctor currentModule exn  in
                  text uu____3671  in
                let uu____3673 =
                  let uu____3677 =
                    let uu____3680 = combine (text ", ") args1  in
                    parens uu____3680  in
                  [uu____3677]  in
                uu____3668 :: uu____3673  in
              (text "raise") :: uu____3664  in
            reduce1 uu____3660
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____3729 =
              let uu____3733 =
                let uu____3737 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____3740 =
                  let uu____3744 =
                    let uu____3748 =
                      let uu____3751 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      combine hardline uu____3751  in
                    [uu____3748]  in
                  (text "with") :: uu____3744  in
                uu____3737 :: uu____3740  in
              (text "try") :: uu____3733  in
            combine hardline uu____3729
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1

and (doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____3801 =
            let uu____3815 = as_bin_op p  in FStar_Option.get uu____3815  in
          match uu____3801 with
          | (uu____3845,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc1 = reduce1 [e11; text txt; e21]  in parens doc1

and (doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____3883 =
          let uu____3890 = as_uni_op p  in FStar_Option.get uu____3890  in
        match uu____3883 with
        | (uu____3906,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 = reduce1 [text txt; parens e11]  in parens doc1

and (doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> doc)
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____3927 = string_of_mlconstant c  in text uu____3927
      | FStar_Extraction_ML_Syntax.MLP_Var x -> text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____3964 =
            match uu____3964 with
            | (name,p) ->
                let uu____3975 =
                  let uu____3979 =
                    let uu____3982 = ptsym currentModule (path, name)  in
                    text uu____3982  in
                  let uu____3988 =
                    let uu____3992 =
                      let uu____3996 = doc_of_pattern currentModule p  in
                      [uu____3996]  in
                    (text "=") :: uu____3992  in
                  uu____3979 :: uu____3988  in
                reduce1 uu____3975
             in
          let uu____4004 =
            let uu____4007 = FStar_List.map for1 fields  in
            combine (text "; ") uu____4007  in
          cbrackets uu____4004
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____4023 = is_standard_constructor ctor  in
            if uu____4023
            then
              let uu____4027 =
                let uu____4034 = as_standard_constructor ctor  in
                FStar_Option.get uu____4034  in
              FStar_Pervasives_Native.snd uu____4027
            else ptctor currentModule ctor  in
          text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____4061 = is_standard_constructor ctor  in
            if uu____4061
            then
              let uu____4065 =
                let uu____4072 = as_standard_constructor ctor  in
                FStar_Option.get uu____4072  in
              FStar_Pervasives_Native.snd uu____4065
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____4104 =
                  let uu____4108 =
                    let uu____4111 = doc_of_pattern currentModule x  in
                    parens uu____4111  in
                  let uu____4114 =
                    let uu____4118 =
                      let uu____4122 = doc_of_pattern currentModule xs  in
                      [uu____4122]  in
                    (text "::") :: uu____4118  in
                  uu____4108 :: uu____4114  in
                reduce uu____4104
            | (uu____4130,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____4131)::[]) ->
                let uu____4138 =
                  let uu____4142 =
                    let uu____4146 =
                      let uu____4149 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____4149  in
                    [uu____4146]  in
                  (text name) :: uu____4142  in
                reduce1 uu____4138
            | uu____4153 ->
                let uu____4161 =
                  let uu____4165 =
                    let uu____4169 =
                      let uu____4172 =
                        let uu____4175 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        combine (text ", ") uu____4175  in
                      parens uu____4172  in
                    [uu____4169]  in
                  (text name) :: uu____4165  in
                reduce1 uu____4161
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____4197 = combine (text ", ") ps1  in parens uu____4197
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map parens ps1  in combine (text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> doc)
  =
  fun currentModule  ->
    fun uu____4217  ->
      match uu____4217 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____4247 =
                  let uu____4251 =
                    let uu____4255 = doc_of_pattern currentModule p  in
                    [uu____4255]  in
                  (text "|") :: uu____4251  in
                reduce1 uu____4247
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____4272 =
                  let uu____4276 =
                    let uu____4280 = doc_of_pattern currentModule p  in
                    [uu____4280; text "when"; c1]  in
                  (text "|") :: uu____4276  in
                reduce1 uu____4272
             in
          let uu____4290 =
            let uu____4294 = reduce1 [case; text "->"; text "begin"]  in
            let uu____4303 =
              let uu____4307 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____4307; text "end"]  in
            uu____4294 :: uu____4303  in
          combine hardline uu____4290

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> doc)
  =
  fun currentModule  ->
    fun uu____4316  ->
      match uu____4316 with
      | (rec_,top_level,lets) ->
          let for1 uu____4367 =
            match uu____4367 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4377;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____4379;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then text ""
                  else
                    (let uu____4405 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____4405
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____4410::uu____4411,uu____4412) -> text ""
                       | FStar_Pervasives_Native.None  -> text ""
                       | FStar_Pervasives_Native.Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty
                              in
                           reduce1 [text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | FStar_Pervasives_Native.None  -> text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              reduce1 [text ":"; ty1]
                          | FStar_Pervasives_Native.Some (vs,ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              let vars =
                                let uu____4452 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____4452 reduce1  in
                              reduce1 [text ":"; vars; text "."; ty1])
                       else text "")
                   in
                let uu____4481 =
                  let uu____4485 =
                    let uu____4489 = reduce1 ids  in
                    [uu____4489; ty_annot; text "="; e1]  in
                  (text name) :: uu____4485  in
                reduce1 uu____4481
             in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then reduce1 [text "let"; text "rec"]
            else text "let"  in
          let lets1 = FStar_List.map for1 lets  in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else text "and";
                     doc1]) lets1
             in
          combine hardline lets2

and (doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> doc) =
  fun uu____4545  ->
    match uu____4545 with
    | (lineno,file) ->
        let uu____4553 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____4553
        then empty
        else
          (let file1 = FStar_Util.basename file  in
           let uu____4563 =
             let uu____4567 =
               let uu____4571 = num lineno  in
               [uu____4571;
               text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))]  in
             (text "#") :: uu____4567  in
           reduce1 uu____4563)

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____4623 =
        match uu____4623 with
        | (uu____4647,x,mangle_opt,tparams,uu____4651,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> empty
              | x2::[] -> text x2
              | uu____4689 ->
                  let doc1 = FStar_List.map (fun x2  -> text x2) tparams  in
                  let uu____4702 = combine (text ", ") doc1  in
                  parens uu____4702
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____4734 =
                    match uu____4734 with
                    | (name,ty) ->
                        let name1 = text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        reduce1 [name1; text ":"; ty1]
                     in
                  let uu____4756 =
                    let uu____4759 = FStar_List.map forfield fields  in
                    combine (text "; ") uu____4759  in
                  cbrackets uu____4756
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____4803 =
                    match uu____4803 with
                    | (name,tys) ->
                        let uu____4835 = FStar_List.split tys  in
                        (match uu____4835 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> text name
                              | uu____4860 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1
                                     in
                                  let tys3 = combine (text " * ") tys2  in
                                  reduce1 [text name; text "of"; tys3]))
                     in
                  let ctors1 = FStar_List.map forctor ctors  in
                  let ctors2 =
                    FStar_List.map (fun d  -> reduce1 [text "|"; d]) ctors1
                     in
                  combine hardline ctors2
               in
            let doc1 =
              let uu____4910 =
                let uu____4914 =
                  let uu____4918 =
                    let uu____4921 = ptsym currentModule ([], x1)  in
                    text uu____4921  in
                  [uu____4918]  in
                tparams1 :: uu____4914  in
              reduce1 uu____4910  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____4936 =
                   let uu____4940 = reduce1 [doc1; text "="]  in
                   [uu____4940; body2]  in
                 combine hardline uu____4936)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____4962 =
            let uu____4966 =
              let uu____4970 = combine (text " \n and ") doc1  in
              [uu____4970]  in
            (text "type") :: uu____4966  in
          reduce1 uu____4962
        else text ""  in
      doc2
  
let rec (doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> doc)
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____5014 =
            let uu____5018 = reduce1 [text "module"; text x; text "="]  in
            let uu____5027 =
              let uu____5031 = doc_of_sig currentModule subsig  in
              let uu____5034 =
                let uu____5038 = reduce1 [text "end"]  in [uu____5038]  in
              uu____5031 :: uu____5034  in
            uu____5018 :: uu____5027  in
          combine hardline uu____5014
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____5073 = combine (text " * ") args1  in parens uu____5073
             in
          reduce1 [text "exception"; text x; text "of"; args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____5085,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
             in
          reduce1 [text "val"; text x; text ": "; ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls

and (doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> doc)
  =
  fun currentModule  ->
    fun s  ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s  in
      let docs1 =
        FStar_List.map (fun x  -> reduce [x; hardline; hardline]) docs  in
      reduce docs1

let (doc_of_mod1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> doc)
  =
  fun currentModule  ->
    fun m  ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,args) ->
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args  in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1
             in
          let args3 =
            let uu____5190 = combine (text " * ") args2  in parens uu____5190
             in
          reduce1 [text "exception"; text x; text "of"; args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____5234 =
            let uu____5238 =
              let uu____5242 =
                let uu____5246 =
                  let uu____5250 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____5250]  in
                (text "=") :: uu____5246  in
              (text "_") :: uu____5242  in
            (text "let") :: uu____5238  in
          reduce1 uu____5234
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
  
let (doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> doc)
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x  in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____5295 -> empty
              | uu____5296 -> hardline);
             hardline]) m
         in
      reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun uu____5314  ->
    match uu____5314 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____5391 =
          match uu____5391 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head1 =
                reduce1 [text "module"; text x1; text ":"; text "sig"]  in
              let tail1 = reduce1 [text "end"]  in
              let doc1 =
                FStar_Option.map
                  (fun uu____5468  ->
                     match uu____5468 with
                     | (s,uu____5475) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map (fun x2  -> reduce [x2; hardline; hardline])
                  sub2
                 in
              let uu____5507 =
                let uu____5511 =
                  let uu____5515 =
                    let uu____5519 = reduce sub3  in
                    [uu____5519; cat tail1 hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> empty
                   | FStar_Pervasives_Native.Some s -> cat s hardline) ::
                    uu____5515
                   in
                (cat head1 hardline) :: uu____5511  in
              reduce uu____5507
        
        and for1_mod istop uu____5533 =
          match uu____5533 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____5622 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [hardline; text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____5648 =
                  let uu____5652 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____5652
                  then [text "module"; text target_mod_name]
                  else
                    if Prims.op_Negation istop
                    then
                      [text "module";
                      text target_mod_name;
                      text "=";
                      text "struct"]
                    else []
                   in
                reduce1 uu____5648  in
              let tail1 =
                if Prims.op_Negation istop
                then reduce1 [text "end"]
                else reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____5702  ->
                     match uu____5702 with
                     | (uu____5708,m) -> doc_of_mod target_mod_name m) sigmod
                 in
              let sub2 = FStar_List.map (for1_mod false) sub1  in
              let sub3 =
                FStar_List.map (fun x  -> reduce [x; hardline; hardline])
                  sub2
                 in
              let prefix1 =
                let uu____5746 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____5746
                then [cat (text "#light \"off\"") hardline]
                else []  in
              let uu____5758 =
                let uu____5762 =
                  let uu____5766 =
                    let uu____5770 =
                      let uu____5774 =
                        let uu____5778 =
                          let uu____5782 = reduce sub3  in
                          [uu____5782; cat tail1 hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  -> empty
                         | FStar_Pervasives_Native.Some s -> cat s hardline)
                          :: uu____5778
                         in
                      hardline :: uu____5774  in
                    FStar_List.append maybe_open_pervasives uu____5770  in
                  FStar_List.append [head1; hardline; text "open Prims"]
                    uu____5766
                   in
                FStar_List.append prefix1 uu____5762  in
              FStar_All.pipe_left reduce uu____5758
         in
        let docs =
          FStar_List.map
            (fun uu____5849  ->
               match uu____5849 with
               | (x,s,m) ->
                   let uu____5910 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____5912 = for1_mod true (x, s, m)  in
                   (uu____5910, uu____5912)) mllib
           in
        docs
  
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____5946  -> match uu____5946 with | Doc doc1 -> doc1 
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____5989 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____5989 (min_op_prec, NonAssoc) e  in
      pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____6007 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____6007 (min_op_prec, NonAssoc) e  in
      pretty (Prims.parse_int "0") doc1
  