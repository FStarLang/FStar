open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_ILeft: assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____4 -> false
let uu___is_IRight: assoc -> Prims.bool =
  fun projectee  -> match projectee with | IRight  -> true | uu____8 -> false
let uu___is_Left: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____12 -> false
let uu___is_Right: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____16 -> false
let uu___is_NonAssoc: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____20 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc[@@deriving show]
let uu___is_Prefix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____28 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____32 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____37 -> false
let __proj__Infix__item___0: fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2[@@deriving show]
let t_prio_fun: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10"), (Infix Right))
let t_prio_tpl: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix NonAssoc))
let t_prio_name: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), Postfix)
let e_bin_prio_lambda: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "5"), Prefix)
let e_bin_prio_if: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "15"), Prefix)
let e_bin_prio_letin: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "19"), Prefix)
let e_bin_prio_or: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix Left))
let e_bin_prio_and: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "25"), (Infix Left))
let e_bin_prio_eq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "27"), (Infix NonAssoc))
let e_bin_prio_order: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "29"), (Infix NonAssoc))
let e_bin_prio_op1: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), (Infix Left))
let e_bin_prio_op2: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "40"), (Infix Left))
let e_bin_prio_op3: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "50"), (Infix Left))
let e_bin_prio_op4: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "60"), (Infix Left))
let e_bin_prio_comb: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "70"), (Infix Left))
let e_bin_prio_seq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "100"), (Infix Left))
let e_app_prio: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10000"), (Infix Left))
let min_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let max_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  (FStar_Util.max_int, (Infix NonAssoc))
let rec in_ns:
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool
  =
  fun x  ->
    match x with
    | ([],uu____152) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____175,uu____176) -> false
let path_of_ns:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun currentModule  ->
    fun ns  ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns in
      if ns' = currentModule
      then []
      else
        (let cg_libs = FStar_Options.codegen_libs () in
         let ns_len = FStar_List.length ns in
         let found =
           FStar_Util.find_map cg_libs
             (fun cg_path  ->
                let cg_len = FStar_List.length cg_path in
                if (FStar_List.length cg_path) < ns_len
                then
                  let uu____234 = FStar_Util.first_N cg_len ns in
                  match uu____234 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____267 =
                           let uu____270 =
                             let uu____273 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____273] in
                           FStar_List.append pfx uu____270 in
                         FStar_Pervasives_Native.Some uu____267
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None) in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____297 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____297 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____302 ->
          let uu____303 = x in
          (match uu____303 with
           | (ns,x1) ->
               let uu____310 = path_of_ns currentModule ns in (uu____310, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____318 =
      let uu____319 =
        let uu____320 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____320 in
      let uu____330 = FStar_String.get s (Prims.parse_int "0") in
      uu____319 <> uu____330 in
    if uu____318 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____355 = mlpath_of_mlpath currentModule mlp in
         match uu____355 with
         | (p,s) ->
             let uu____362 =
               let uu____365 =
                 let uu____368 = ptsym_of_symbol s in [uu____368] in
               FStar_List.append p uu____365 in
             FStar_String.concat "." uu____362)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____375 = mlpath_of_mlpath currentModule mlp in
      match uu____375 with
      | (p,s) ->
          let s1 =
            let uu____383 =
              let uu____384 =
                let uu____385 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____385 in
              let uu____395 = FStar_String.get s (Prims.parse_int "0") in
              uu____384 <> uu____395 in
            if uu____383 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s1])
let infix_prim_ops:
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list
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
let prim_uni_ops:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____635  ->
    let op_minus =
      let uu____637 = FStar_Options.codegen_fsharp () in
      if uu____637 then "-" else "~-" in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
let prim_types: 'Auu____656 . Prims.unit -> 'Auu____656 Prims.list =
  fun uu____659  -> []
let prim_constructors:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option
  =
  fun uu____709  ->
    match uu____709 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____754  ->
               match uu____754 with | (y,uu____766,uu____767) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____790 = as_bin_op p in uu____790 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____833  ->
    match uu____833 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____852 = prim_uni_ops () in
          FStar_List.tryFind
            (fun uu____866  -> match uu____866 with | (y,uu____872) -> x = y)
            uu____852
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____881 = as_uni_op p in uu____881 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____909  ->
    match uu____909 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____935  -> match uu____935 with | (y,uu____941) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____950 = as_standard_constructor p in
    uu____950 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____985  ->
    fun inner  ->
      fun doc1  ->
        match uu____985 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1036 = _inner in
              match uu____1036 with
              | (pi,fi) ->
                  let uu____1043 = _outer in
                  (match uu____1043 with
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
                           | (uu____1050,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1051,uu____1052) -> false))) in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
let escape_byte_hex: FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let escape_char_hex: FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___378_1092  ->
      match uu___378_1092 with
      | c when c = 92 -> "\\\\"
      | c when c = 32 -> " "
      | c when c = 8 -> "\\b"
      | c when c = 9 -> "\\t"
      | c when c = 13 -> "\\r"
      | c when c = 10 -> "\\n"
      | c when c = 39 -> "\\'"
      | c when c = 34 -> "\\\""
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let string_of_mlconstant:
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c in
        let uu____1241 = FStar_Util.string_of_int nc in
        Prims.strcat uu____1241
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
        (s,FStar_Pervasives_Native.Some (uu____1330,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1342,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1368 =
          let uu____1369 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1369 "\"" in
        Prims.strcat "\"" uu____1368
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1371 =
          let uu____1372 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1372 "\"" in
        Prims.strcat "\"" uu____1371
    | uu____1373 ->
        failwith "TODO: extract integer constants properly into OCaml"
let rec doc_of_mltype':
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s 95 117
              else s in
            FStar_Format.text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____1406 =
                let uu____1407 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1407 in
              FStar_Format.parens uu____1406 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1420 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1430 =
                    let uu____1431 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1431 in
                  FStar_Format.parens uu____1430 in
            let name1 = ptsym currentModule name in
            let uu____1433 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1433
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1435,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1447 =
              let uu____1448 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1448 in
            maybe_paren outer t_prio_fun uu____1447
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1449 = FStar_Options.codegen_fsharp () in
            if uu____1449
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1454 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1454
let rec doc_of_expr:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let uu____1508 = FStar_Options.codegen_fsharp () in
            if uu____1508
            then
              let uu____1509 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1] in
              FStar_Format.parens uu____1509
            else
              (let uu____1511 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1511)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs1 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs in
            let uu____1527 = FStar_Format.reduce docs1 in
            FStar_Format.parens uu____1527
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1529 = string_of_mlconstant c in
            FStar_Format.text uu____1529
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1532 = ptsym currentModule path in
            FStar_Format.text uu____1532
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1558 =
              match uu____1558 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1570 =
                    let uu____1573 =
                      let uu____1574 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1574 in
                    [uu____1573; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1570 in
            let uu____1577 =
              let uu____1578 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1578 in
            FStar_Format.cbrackets uu____1577
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1589 = is_standard_constructor ctor in
              if uu____1589
              then
                let uu____1590 =
                  let uu____1595 = as_standard_constructor ctor in
                  FStar_Option.get uu____1595 in
                FStar_Pervasives_Native.snd uu____1590
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1614 = is_standard_constructor ctor in
              if uu____1614
              then
                let uu____1615 =
                  let uu____1620 = as_standard_constructor ctor in
                  FStar_Option.get uu____1620 in
                FStar_Pervasives_Native.snd uu____1615
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1646,uu____1647) ->
                  let uu____1652 =
                    let uu____1655 =
                      let uu____1658 =
                        let uu____1659 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1659 in
                      [uu____1658] in
                    (FStar_Format.text name) :: uu____1655 in
                  FStar_Format.reduce1 uu____1652 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____1669 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1669) es in
            let docs1 =
              let uu____1675 =
                FStar_Format.combine (FStar_Format.text ", ") docs in
              FStar_Format.parens uu____1675 in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1677,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1693 =
                  let uu____1696 =
                    let uu____1699 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1699] in
                  FStar_Format.hardline :: uu____1696 in
                FStar_Format.reduce uu____1693
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1709 =
              let uu____1710 =
                let uu____1713 =
                  let uu____1716 =
                    let uu____1719 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1719] in
                  doc1 :: uu____1716 in
                pre :: uu____1713 in
              FStar_Format.combine FStar_Format.hardline uu____1710 in
            FStar_Format.parens uu____1709
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1729::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1731;
                    FStar_Extraction_ML_Syntax.loc = uu____1732;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1734)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1736;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1737;_}::[])
                 when
                 let uu____1772 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1772 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1795;
                            FStar_Extraction_ML_Syntax.loc = uu____1796;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1798;
                       FStar_Extraction_ML_Syntax.loc = uu____1799;_} when
                       arg = arg' -> branches
                   | e2 ->
                       [(FStar_Extraction_ML_Syntax.MLP_Wild,
                          FStar_Pervasives_Native.None, e2)] in
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1855;
                   FStar_Extraction_ML_Syntax.loc = uu____1856;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1869;
                   FStar_Extraction_ML_Syntax.loc = uu____1870;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1877 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1896 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1896)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1905 = FStar_Options.codegen_fsharp () in
              if uu____1905
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1909 =
                   let uu____1912 =
                     let uu____1915 =
                       let uu____1918 =
                         let uu____1919 = ptsym currentModule f in
                         FStar_Format.text uu____1919 in
                       [uu____1918] in
                     (FStar_Format.text ".") :: uu____1915 in
                   e2 :: uu____1912 in
                 FStar_Format.reduce uu____1909) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1945 = FStar_Options.codegen_fsharp () in
              if uu____1945
              then
                let uu____1946 =
                  let uu____1949 =
                    let uu____1952 =
                      let uu____1955 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1957 =
                              let uu____1960 =
                                let uu____1963 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1963] in
                              (FStar_Format.text " : ") :: uu____1960 in
                            FStar_Format.reduce1 uu____1957
                        | uu____1964 -> FStar_Format.text "" in
                      [uu____1955; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1952 in
                  (FStar_Format.text "(") :: uu____1949 in
                FStar_Format.reduce1 uu____1946
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1978  ->
                   match uu____1978 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1991 =
                let uu____1994 =
                  let uu____1997 = FStar_Format.reduce1 ids1 in
                  [uu____1997; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1994 in
              FStar_Format.reduce1 uu____1991 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____2008 =
                let uu____2011 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____2012 =
                  let uu____2015 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____2015; FStar_Format.text "end"] in
                uu____2011 :: uu____2012 in
              FStar_Format.combine FStar_Format.hardline uu____2008 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____2031 =
                let uu____2034 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____2035 =
                  let uu____2038 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____2043 =
                    let uu____2046 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____2047 =
                      let uu____2050 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____2050; FStar_Format.text "end"] in
                    uu____2046 :: uu____2047 in
                  uu____2038 :: uu____2043 in
                uu____2034 :: uu____2035 in
              FStar_Format.combine FStar_Format.hardline uu____2031 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____2088 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____2088 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2093 =
              let uu____2096 =
                let uu____2099 =
                  let uu____2100 = ptctor currentModule exn in
                  FStar_Format.text uu____2100 in
                [uu____2099] in
              (FStar_Format.text "raise") :: uu____2096 in
            FStar_Format.reduce1 uu____2093
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____2114 =
              let uu____2117 =
                let uu____2120 =
                  let uu____2121 = ptctor currentModule exn in
                  FStar_Format.text uu____2121 in
                let uu____2122 =
                  let uu____2125 =
                    let uu____2126 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____2126 in
                  [uu____2125] in
                uu____2120 :: uu____2122 in
              (FStar_Format.text "raise") :: uu____2117 in
            FStar_Format.reduce1 uu____2114
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2149 =
              let uu____2152 =
                let uu____2155 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____2160 =
                  let uu____2163 =
                    let uu____2166 =
                      let uu____2167 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____2167 in
                    [uu____2166] in
                  (FStar_Format.text "with") :: uu____2163 in
                uu____2155 :: uu____2160 in
              (FStar_Format.text "try") :: uu____2152 in
            FStar_Format.combine FStar_Format.hardline uu____2149
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1
and doc_of_binop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____2180 =
            let uu____2191 = as_bin_op p in FStar_Option.get uu____2191 in
          match uu____2180 with
          | (uu____2214,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1 in
              let e21 = doc_of_expr currentModule (prio, Right) e2 in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21] in
              FStar_Format.parens doc1
and doc_of_uniop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____2239 =
          let uu____2244 = as_uni_op p in FStar_Option.get uu____2244 in
        match uu____2239 with
        | (uu____2255,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11] in
            FStar_Format.parens doc1
and doc_of_pattern:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____2266 = string_of_mlconstant c in
          FStar_Format.text uu____2266
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2293 =
            match uu____2293 with
            | (name,p) ->
                let uu____2300 =
                  let uu____2303 =
                    let uu____2304 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2304 in
                  let uu____2307 =
                    let uu____2310 =
                      let uu____2313 = doc_of_pattern currentModule p in
                      [uu____2313] in
                    (FStar_Format.text "=") :: uu____2310 in
                  uu____2303 :: uu____2307 in
                FStar_Format.reduce1 uu____2300 in
          let uu____2314 =
            let uu____2315 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2315 in
          FStar_Format.cbrackets uu____2314
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2326 = is_standard_constructor ctor in
            if uu____2326
            then
              let uu____2327 =
                let uu____2332 = as_standard_constructor ctor in
                FStar_Option.get uu____2332 in
              FStar_Pervasives_Native.snd uu____2327
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2351 = is_standard_constructor ctor in
            if uu____2351
            then
              let uu____2352 =
                let uu____2357 = as_standard_constructor ctor in
                FStar_Option.get uu____2357 in
              FStar_Pervasives_Native.snd uu____2352
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2376 =
                  let uu____2379 =
                    let uu____2380 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2380 in
                  let uu____2381 =
                    let uu____2384 =
                      let uu____2387 = doc_of_pattern currentModule xs in
                      [uu____2387] in
                    (FStar_Format.text "::") :: uu____2384 in
                  uu____2379 :: uu____2381 in
                FStar_Format.reduce uu____2376
            | (uu____2388,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2389)::[]) ->
                let uu____2394 =
                  let uu____2397 =
                    let uu____2400 =
                      let uu____2401 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2401 in
                    [uu____2400] in
                  (FStar_Format.text name) :: uu____2397 in
                FStar_Format.reduce1 uu____2394
            | uu____2402 ->
                let uu____2409 =
                  let uu____2412 =
                    let uu____2415 =
                      let uu____2416 =
                        let uu____2417 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2417 in
                      FStar_Format.parens uu____2416 in
                    [uu____2415] in
                  (FStar_Format.text name) :: uu____2412 in
                FStar_Format.reduce1 uu____2409 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2430 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2430
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2441  ->
      match uu____2441 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2450 =
                  let uu____2453 =
                    let uu____2456 = doc_of_pattern currentModule p in
                    [uu____2456] in
                  (FStar_Format.text "|") :: uu____2453 in
                FStar_Format.reduce1 uu____2450
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2463 =
                  let uu____2466 =
                    let uu____2469 = doc_of_pattern currentModule p in
                    [uu____2469; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2466 in
                FStar_Format.reduce1 uu____2463 in
          let uu____2470 =
            let uu____2473 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2474 =
              let uu____2477 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2477; FStar_Format.text "end"] in
            uu____2473 :: uu____2474 in
          FStar_Format.combine FStar_Format.hardline uu____2470
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2483  ->
      match uu____2483 with
      | (rec_,top_level,lets) ->
          let for1 uu____2502 =
            match uu____2502 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2505;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2520 =
                       (FStar_Options.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2520
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2521::uu____2522,uu____2523) ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.None  ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
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
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1]
                          | FStar_Pervasives_Native.Some (vs,ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              let vars =
                                let uu____2575 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu____2575
                                  FStar_Format.reduce1 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "") in
                let uu____2589 =
                  let uu____2592 =
                    let uu____2595 = FStar_Format.reduce1 ids in
                    [uu____2595; ty_annot; FStar_Format.text "="; e1] in
                  (FStar_Format.text name) :: uu____2592 in
                FStar_Format.reduce1 uu____2589 in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then
              FStar_Format.reduce1
                [FStar_Format.text "let"; FStar_Format.text "rec"]
            else FStar_Format.text "let" in
          let lets1 = FStar_List.map for1 lets in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   FStar_Format.reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else FStar_Format.text "and";
                     doc1]) lets1 in
          FStar_Format.combine FStar_Format.hardline lets2
and doc_of_loc: FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____2609  ->
    match uu____2609 with
    | (lineno,file) ->
        let uu____2612 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Options.codegen_fsharp ()) in
        if uu____2612
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])
let doc_of_mltydecl:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____2642 =
        match uu____2642 with
        | (uu____2661,x,mangle_opt,tparams,uu____2665,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2683 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams in
                  let uu____2691 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2691 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2715 =
                    match uu____2715 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2728 =
                    let uu____2729 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2729 in
                  FStar_Format.cbrackets uu____2728
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2762 =
                    match uu____2762 with
                    | (name,tys) ->
                        let uu____2787 = FStar_List.split tys in
                        (match uu____2787 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2806 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1 in
                                  let tys3 =
                                    FStar_Format.combine
                                      (FStar_Format.text " * ") tys2 in
                                  FStar_Format.reduce1
                                    [FStar_Format.text name;
                                    FStar_Format.text "of";
                                    tys3])) in
                  let ctors1 = FStar_List.map forctor ctors in
                  let ctors2 =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors1 in
                  FStar_Format.combine FStar_Format.hardline ctors2 in
            let doc1 =
              let uu____2836 =
                let uu____2839 =
                  let uu____2842 =
                    let uu____2843 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2843 in
                  [uu____2842] in
                tparams1 :: uu____2839 in
              FStar_Format.reduce1 uu____2836 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2848 =
                   let uu____2851 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2851; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2848) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2874 =
            let uu____2877 =
              let uu____2880 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2880] in
            (FStar_Format.text "type") :: uu____2877 in
          FStar_Format.reduce1 uu____2874
        else FStar_Format.text "" in
      doc2
let rec doc_of_sig1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____2898 =
            let uu____2901 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____2902 =
              let uu____2905 = doc_of_sig currentModule subsig in
              let uu____2906 =
                let uu____2909 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____2909] in
              uu____2905 :: uu____2906 in
            uu____2901 :: uu____2902 in
          FStar_Format.combine FStar_Format.hardline uu____2898
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____2927 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____2927 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2929,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and doc_of_sig:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs1 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs in
      FStar_Format.reduce docs1
let doc_of_mod1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,args) ->
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1 in
          let args3 =
            let uu____2997 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____2997 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____3000,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____3009 =
            let uu____3012 =
              let uu____3015 =
                let uu____3018 =
                  let uu____3021 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____3021] in
                (FStar_Format.text "=") :: uu____3018 in
              (FStar_Format.text "_") :: uu____3015 in
            (FStar_Format.text "let") :: uu____3012 in
          FStar_Format.reduce1 uu____3009
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let doc_of_mod:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____3045 ->
                  FStar_Format.empty
              | uu____3046 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3055  ->
    match uu____3055 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3121 =
          match uu____3121 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head1 =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x1;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"] in
              let tail1 = FStar_Format.reduce1 [FStar_Format.text "end"] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3194  ->
                     match uu____3194 with
                     | (s,uu____3200) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____3227 =
                let uu____3230 =
                  let uu____3233 =
                    let uu____3236 = FStar_Format.reduce sub3 in
                    [uu____3236;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3233 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3230 in
              FStar_Format.reduce uu____3227
        and for1_mod istop uu____3239 =
          match uu____3239 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1 in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3307 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3318 =
                  let uu____3321 = FStar_Options.codegen_fsharp () in
                  if uu____3321
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
                    else [] in
                FStar_Format.reduce1 uu____3318 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3340  ->
                     match uu____3340 with
                     | (uu____3345,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3376 = FStar_Options.codegen_fsharp () in
                if uu____3376
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3380 =
                let uu____3383 =
                  let uu____3386 =
                    let uu____3389 =
                      let uu____3392 =
                        let uu____3395 =
                          let uu____3398 = FStar_Format.reduce sub3 in
                          [uu____3398;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3395 in
                      FStar_Format.hardline :: uu____3392 in
                    FStar_List.append maybe_open_pervasives uu____3389 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3386 in
                FStar_List.append prefix1 uu____3383 in
              FStar_All.pipe_left FStar_Format.reduce uu____3380 in
        let docs =
          FStar_List.map
            (fun uu____3437  ->
               match uu____3437 with
               | (x,s,m) ->
                   let uu____3487 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3488 = for1_mod true (x, s, m) in
                   (uu____3487, uu____3488)) mllib in
        docs
let doc_of_mllib:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib
let string_of_mlexpr:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3517 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3517 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3529 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3529 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1