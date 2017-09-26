open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_ILeft: assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____5 -> false
let uu___is_IRight: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____10 -> false
let uu___is_Left: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____15 -> false
let uu___is_Right: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____20 -> false
let uu___is_NonAssoc: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____25 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc[@@deriving show]
let uu___is_Prefix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____34 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____39 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____45 -> false
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
    | ([],uu____163) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____186,uu____187) -> false
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
                  let uu____247 = FStar_Util.first_N cg_len ns in
                  match uu____247 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____280 =
                           let uu____283 =
                             let uu____286 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____286] in
                           FStar_List.append pfx uu____283 in
                         FStar_Pervasives_Native.Some uu____280
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
      let uu____312 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____312 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____317 ->
          let uu____318 = x in
          (match uu____318 with
           | (ns,x1) ->
               let uu____325 = path_of_ns currentModule ns in (uu____325, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____334 =
      let uu____335 =
        let uu____336 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____336 in
      let uu____349 = FStar_String.get s (Prims.parse_int "0") in
      uu____335 <> uu____349 in
    if uu____334 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____380 = mlpath_of_mlpath currentModule mlp in
         match uu____380 with
         | (p,s) ->
             let uu____387 =
               let uu____390 =
                 let uu____393 = ptsym_of_symbol s in [uu____393] in
               FStar_List.append p uu____390 in
             FStar_String.concat "." uu____387)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____402 = mlpath_of_mlpath currentModule mlp in
      match uu____402 with
      | (p,s) ->
          let s1 =
            let uu____410 =
              let uu____411 =
                let uu____412 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____412 in
              let uu____425 = FStar_String.get s (Prims.parse_int "0") in
              uu____411 <> uu____425 in
            if uu____410 then Prims.strcat "U__" s else s in
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
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")]
let prim_types: 'Auu____685 . Prims.unit -> 'Auu____685 Prims.list =
  fun uu____688  -> []
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
  fun uu____740  ->
    match uu____740 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____785  ->
               match uu____785 with | (y,uu____797,uu____798) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____822 = as_bin_op p in uu____822 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____866  ->
    match uu____866 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____892  -> match uu____892 with | (y,uu____898) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____908 = as_uni_op p in uu____908 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____938  ->
    match uu____938 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____964  -> match uu____964 with | (y,uu____970) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____980 = as_standard_constructor p in
    uu____980 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____1018  ->
    fun inner  ->
      fun doc1  ->
        match uu____1018 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1069 = _inner in
              match uu____1069 with
              | (pi,fi) ->
                  let uu____1076 = _outer in
                  (match uu____1076 with
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
                           | (uu____1083,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1084,uu____1085) -> false))) in
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
    fun uu___126_1137  ->
      match uu___126_1137 with
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
        let uu____1330 = FStar_Util.string_of_int nc in
        Prims.strcat uu____1330
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
        (s,FStar_Pervasives_Native.Some (uu____1422,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1434,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1460 =
          let uu____1461 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1461 "\"" in
        Prims.strcat "\"" uu____1460
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1463 =
          let uu____1464 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1464 "\"" in
        Prims.strcat "\"" uu____1463
    | uu____1465 ->
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
            let uu____1487 =
              let uu____1488 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____1488 in
            FStar_Format.text uu____1487
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____1500 =
                let uu____1501 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1501 in
              FStar_Format.parens uu____1500 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1514 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1524 =
                    let uu____1525 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1525 in
                  FStar_Format.parens uu____1524 in
            let name1 = ptsym currentModule name in
            let uu____1527 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1527
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1529,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1541 =
              let uu____1542 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1542 in
            maybe_paren outer t_prio_fun uu____1541
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1543 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1543
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1548 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1548
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
            let uu____1602 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1602
            then
              let uu____1603 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____1603
            else
              (let uu____1605 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1605)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____1621 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____1621
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1623 = string_of_mlconstant c in
            FStar_Format.text uu____1623
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____1625) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1627 = ptsym currentModule path in
            FStar_Format.text uu____1627
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1653 =
              match uu____1653 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1665 =
                    let uu____1668 =
                      let uu____1669 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1669 in
                    [uu____1668; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1665 in
            let uu____1672 =
              let uu____1673 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1673 in
            FStar_Format.cbrackets uu____1672
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1684 = is_standard_constructor ctor in
              if uu____1684
              then
                let uu____1685 =
                  let uu____1690 = as_standard_constructor ctor in
                  FStar_Option.get uu____1690 in
                FStar_Pervasives_Native.snd uu____1685
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1709 = is_standard_constructor ctor in
              if uu____1709
              then
                let uu____1710 =
                  let uu____1715 = as_standard_constructor ctor in
                  FStar_Option.get uu____1715 in
                FStar_Pervasives_Native.snd uu____1710
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1741,uu____1742) ->
                  let uu____1747 =
                    let uu____1750 =
                      let uu____1753 =
                        let uu____1754 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1754 in
                      [uu____1753] in
                    (FStar_Format.text name) :: uu____1750 in
                  FStar_Format.reduce1 uu____1747 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____1764 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1764) es in
            let docs2 =
              let uu____1770 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____1770 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1772,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1788 =
                  let uu____1791 =
                    let uu____1794 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1794] in
                  FStar_Format.hardline :: uu____1791 in
                FStar_Format.reduce uu____1788
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1804 =
              let uu____1805 =
                let uu____1808 =
                  let uu____1811 =
                    let uu____1814 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1814] in
                  doc1 :: uu____1811 in
                pre :: uu____1808 in
              FStar_Format.combine FStar_Format.hardline uu____1805 in
            FStar_Format.parens uu____1804
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1824::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1826;
                    FStar_Extraction_ML_Syntax.loc = uu____1827;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1829)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1831;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1832;_}::[])
                 when
                 let uu____1867 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1867 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1890;
                            FStar_Extraction_ML_Syntax.loc = uu____1891;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1893;
                       FStar_Extraction_ML_Syntax.loc = uu____1894;_} when
                       let uu____1915 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1916 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1915 = uu____1916 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1952;
                   FStar_Extraction_ML_Syntax.loc = uu____1953;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1966;
                   FStar_Extraction_ML_Syntax.loc = uu____1967;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1974 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1993 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1993)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____2002 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____2002
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2006 =
                   let uu____2009 =
                     let uu____2012 =
                       let uu____2015 =
                         let uu____2016 = ptsym currentModule f in
                         FStar_Format.text uu____2016 in
                       [uu____2015] in
                     (FStar_Format.text ".") :: uu____2012 in
                   e2 :: uu____2009 in
                 FStar_Format.reduce uu____2006) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2042 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____2042
              then
                let uu____2043 =
                  let uu____2046 =
                    let uu____2049 =
                      let uu____2052 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2054 =
                              let uu____2057 =
                                let uu____2060 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____2060] in
                              (FStar_Format.text " : ") :: uu____2057 in
                            FStar_Format.reduce1 uu____2054
                        | uu____2061 -> FStar_Format.text "" in
                      [uu____2052; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____2049 in
                  (FStar_Format.text "(") :: uu____2046 in
                FStar_Format.reduce1 uu____2043
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____2080  ->
                   match uu____2080 with
                   | ((x,uu____2090),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____2102 =
                let uu____2105 =
                  let uu____2108 = FStar_Format.reduce1 ids1 in
                  [uu____2108; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____2105 in
              FStar_Format.reduce1 uu____2102 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____2119 =
                let uu____2122 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____2123 =
                  let uu____2126 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____2126; FStar_Format.text "end"] in
                uu____2122 :: uu____2123 in
              FStar_Format.combine FStar_Format.hardline uu____2119 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____2142 =
                let uu____2145 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____2146 =
                  let uu____2149 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____2154 =
                    let uu____2157 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____2158 =
                      let uu____2161 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____2161; FStar_Format.text "end"] in
                    uu____2157 :: uu____2158 in
                  uu____2149 :: uu____2154 in
                uu____2145 :: uu____2146 in
              FStar_Format.combine FStar_Format.hardline uu____2142 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____2199 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____2199 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2204 =
              let uu____2207 =
                let uu____2210 =
                  let uu____2211 = ptctor currentModule exn in
                  FStar_Format.text uu____2211 in
                [uu____2210] in
              (FStar_Format.text "raise") :: uu____2207 in
            FStar_Format.reduce1 uu____2204
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____2225 =
              let uu____2228 =
                let uu____2231 =
                  let uu____2232 = ptctor currentModule exn in
                  FStar_Format.text uu____2232 in
                let uu____2233 =
                  let uu____2236 =
                    let uu____2237 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____2237 in
                  [uu____2236] in
                uu____2231 :: uu____2233 in
              (FStar_Format.text "raise") :: uu____2228 in
            FStar_Format.reduce1 uu____2225
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2260 =
              let uu____2263 =
                let uu____2266 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____2271 =
                  let uu____2274 =
                    let uu____2277 =
                      let uu____2278 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____2278 in
                    [uu____2277] in
                  (FStar_Format.text "with") :: uu____2274 in
                uu____2266 :: uu____2271 in
              (FStar_Format.text "try") :: uu____2263 in
            FStar_Format.combine FStar_Format.hardline uu____2260
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
          let uu____2291 =
            let uu____2302 = as_bin_op p in FStar_Option.get uu____2302 in
          match uu____2291 with
          | (uu____2325,prio,txt) ->
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
        let uu____2350 =
          let uu____2355 = as_uni_op p in FStar_Option.get uu____2355 in
        match uu____2350 with
        | (uu____2366,txt) ->
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
          let uu____2377 = string_of_mlconstant c in
          FStar_Format.text uu____2377
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2404 =
            match uu____2404 with
            | (name,p) ->
                let uu____2411 =
                  let uu____2414 =
                    let uu____2415 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2415 in
                  let uu____2418 =
                    let uu____2421 =
                      let uu____2424 = doc_of_pattern currentModule p in
                      [uu____2424] in
                    (FStar_Format.text "=") :: uu____2421 in
                  uu____2414 :: uu____2418 in
                FStar_Format.reduce1 uu____2411 in
          let uu____2425 =
            let uu____2426 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2426 in
          FStar_Format.cbrackets uu____2425
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2437 = is_standard_constructor ctor in
            if uu____2437
            then
              let uu____2438 =
                let uu____2443 = as_standard_constructor ctor in
                FStar_Option.get uu____2443 in
              FStar_Pervasives_Native.snd uu____2438
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2462 = is_standard_constructor ctor in
            if uu____2462
            then
              let uu____2463 =
                let uu____2468 = as_standard_constructor ctor in
                FStar_Option.get uu____2468 in
              FStar_Pervasives_Native.snd uu____2463
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2487 =
                  let uu____2490 =
                    let uu____2491 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2491 in
                  let uu____2492 =
                    let uu____2495 =
                      let uu____2498 = doc_of_pattern currentModule xs in
                      [uu____2498] in
                    (FStar_Format.text "::") :: uu____2495 in
                  uu____2490 :: uu____2492 in
                FStar_Format.reduce uu____2487
            | (uu____2499,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2500)::[]) ->
                let uu____2505 =
                  let uu____2508 =
                    let uu____2511 =
                      let uu____2512 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2512 in
                    [uu____2511] in
                  (FStar_Format.text name) :: uu____2508 in
                FStar_Format.reduce1 uu____2505
            | uu____2513 ->
                let uu____2520 =
                  let uu____2523 =
                    let uu____2526 =
                      let uu____2527 =
                        let uu____2528 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2528 in
                      FStar_Format.parens uu____2527 in
                    [uu____2526] in
                  (FStar_Format.text name) :: uu____2523 in
                FStar_Format.reduce1 uu____2520 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2541 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2541
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2552  ->
      match uu____2552 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2561 =
                  let uu____2564 =
                    let uu____2567 = doc_of_pattern currentModule p in
                    [uu____2567] in
                  (FStar_Format.text "|") :: uu____2564 in
                FStar_Format.reduce1 uu____2561
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2574 =
                  let uu____2577 =
                    let uu____2580 = doc_of_pattern currentModule p in
                    [uu____2580; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2577 in
                FStar_Format.reduce1 uu____2574 in
          let uu____2581 =
            let uu____2584 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2585 =
              let uu____2588 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2588; FStar_Format.text "end"] in
            uu____2584 :: uu____2585 in
          FStar_Format.combine FStar_Format.hardline uu____2581
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2594  ->
      match uu____2594 with
      | (rec_,top_level,lets) ->
          let for1 uu____2613 =
            match uu____2613 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2616;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2631 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2631
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2632::uu____2633,uu____2634) ->
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
                                let uu____2686 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu____2686
                                  FStar_Format.reduce1 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "") in
                let uu____2700 =
                  let uu____2703 =
                    let uu____2704 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____2704 in
                  let uu____2705 =
                    let uu____2708 = FStar_Format.reduce1 ids in
                    [uu____2708; ty_annot; FStar_Format.text "="; e1] in
                  uu____2703 :: uu____2705 in
                FStar_Format.reduce1 uu____2700 in
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
  fun uu____2722  ->
    match uu____2722 with
    | (lineno,file) ->
        let uu____2725 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____2725
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
      let for1 uu____2757 =
        match uu____2757 with
        | (uu____2776,x,mangle_opt,tparams,uu____2780,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____2798 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____2798
              | uu____2799 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____2808 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____2808) tparams in
                  let uu____2809 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2809 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2833 =
                    match uu____2833 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2846 =
                    let uu____2847 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2847 in
                  FStar_Format.cbrackets uu____2846
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2880 =
                    match uu____2880 with
                    | (name,tys) ->
                        let uu____2905 = FStar_List.split tys in
                        (match uu____2905 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2924 ->
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
              let uu____2954 =
                let uu____2957 =
                  let uu____2960 =
                    let uu____2961 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2961 in
                  [uu____2960] in
                tparams1 :: uu____2957 in
              FStar_Format.reduce1 uu____2954 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2966 =
                   let uu____2969 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2969; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2966) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2992 =
            let uu____2995 =
              let uu____2998 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2998] in
            (FStar_Format.text "type") :: uu____2995 in
          FStar_Format.reduce1 uu____2992
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
          let uu____3016 =
            let uu____3019 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____3020 =
              let uu____3023 = doc_of_sig currentModule subsig in
              let uu____3024 =
                let uu____3027 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____3027] in
              uu____3023 :: uu____3024 in
            uu____3019 :: uu____3020 in
          FStar_Format.combine FStar_Format.hardline uu____3016
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____3045 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____3045 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3047,ty)) ->
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
      let docs1 = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs2 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs1 in
      FStar_Format.reduce docs2
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
            let uu____3117 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____3117 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____3120,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____3129 =
            let uu____3132 =
              let uu____3135 =
                let uu____3138 =
                  let uu____3141 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____3141] in
                (FStar_Format.text "=") :: uu____3138 in
              (FStar_Format.text "_") :: uu____3135 in
            (FStar_Format.text "let") :: uu____3132 in
          FStar_Format.reduce1 uu____3129
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let doc_of_mod:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs1 =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____3167 ->
                  FStar_Format.empty
              | uu____3168 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3178  ->
    match uu____3178 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3244 =
          match uu____3244 with
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
                  (fun uu____3317  ->
                     match uu____3317 with
                     | (s,uu____3323) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____3350 =
                let uu____3353 =
                  let uu____3356 =
                    let uu____3359 = FStar_Format.reduce sub3 in
                    [uu____3359;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3356 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3353 in
              FStar_Format.reduce uu____3350
        and for1_mod istop uu____3362 =
          match uu____3362 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3430 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3441 =
                  let uu____3444 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____3444
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
                FStar_Format.reduce1 uu____3441 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3463  ->
                     match uu____3463 with
                     | (uu____3468,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3499 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____3499
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3503 =
                let uu____3506 =
                  let uu____3509 =
                    let uu____3512 =
                      let uu____3515 =
                        let uu____3518 =
                          let uu____3521 = FStar_Format.reduce sub3 in
                          [uu____3521;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3518 in
                      FStar_Format.hardline :: uu____3515 in
                    FStar_List.append maybe_open_pervasives uu____3512 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3509 in
                FStar_List.append prefix1 uu____3506 in
              FStar_All.pipe_left FStar_Format.reduce uu____3503 in
        let docs1 =
          FStar_List.map
            (fun uu____3560  ->
               match uu____3560 with
               | (x,s,m) ->
                   let uu____3610 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3611 = for1_mod true (x, s, m) in
                   (uu____3610, uu____3611)) mllib in
        docs1
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
        let uu____3643 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3643 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3657 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3657 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1