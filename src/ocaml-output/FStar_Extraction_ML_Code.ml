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
    | ([],uu____153) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____176,uu____177) -> false
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
                  let uu____235 = FStar_Util.first_N cg_len ns in
                  match uu____235 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____268 =
                           let uu____271 =
                             let uu____274 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____274] in
                           FStar_List.append pfx uu____271 in
                         FStar_Pervasives_Native.Some uu____268
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
      let uu____298 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____298 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____303 ->
          let uu____304 = x in
          (match uu____304 with
           | (ns,x1) ->
               let uu____311 = path_of_ns currentModule ns in (uu____311, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____319 =
      let uu____320 =
        let uu____321 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____321 in
      let uu____322 = FStar_String.get s (Prims.parse_int "0") in
      uu____320 <> uu____322 in
    if uu____319 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____335 = mlpath_of_mlpath currentModule mlp in
         match uu____335 with
         | (p,s) ->
             let uu____342 =
               let uu____345 =
                 let uu____348 = ptsym_of_symbol s in [uu____348] in
               FStar_List.append p uu____345 in
             FStar_String.concat "." uu____342)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____355 = mlpath_of_mlpath currentModule mlp in
      match uu____355 with
      | (p,s) ->
          let s1 =
            let uu____363 =
              let uu____364 =
                let uu____365 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____365 in
              let uu____366 = FStar_String.get s (Prims.parse_int "0") in
              uu____364 <> uu____366 in
            if uu____363 then Prims.strcat "U__" s else s in
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
  fun uu____594  ->
    let op_minus =
      let uu____596 = FStar_Options.codegen_fsharp () in
      if uu____596 then "-" else "~-" in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
let prim_types: 'Auu____615 . Prims.unit -> 'Auu____615 Prims.list =
  fun uu____618  -> []
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
  fun uu____668  ->
    match uu____668 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____713  ->
               match uu____713 with | (y,uu____725,uu____726) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____749 = as_bin_op p in uu____749 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____792  ->
    match uu____792 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____811 = prim_uni_ops () in
          FStar_List.tryFind
            (fun uu____825  -> match uu____825 with | (y,uu____831) -> x = y)
            uu____811
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____840 = as_uni_op p in uu____840 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____868  ->
    match uu____868 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____894  -> match uu____894 with | (y,uu____900) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____909 = as_standard_constructor p in
    uu____909 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____944  ->
    fun inner  ->
      fun doc1  ->
        match uu____944 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____995 = _inner in
              match uu____995 with
              | (pi,fi) ->
                  let uu____1002 = _outer in
                  (match uu____1002 with
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
                           | (uu____1009,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1010,uu____1011) -> false))) in
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
    fun uu___377_1027  ->
      match uu___377_1027 with
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
        let uu____1047 = FStar_Util.string_of_int nc in
        Prims.strcat uu____1047
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
        (s,FStar_Pervasives_Native.Some (uu____1116,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1128,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1154 =
          let uu____1155 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1155 "\"" in
        Prims.strcat "\"" uu____1154
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1157 =
          let uu____1158 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1158 "\"" in
        Prims.strcat "\"" uu____1157
    | uu____1159 ->
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
              let uu____1192 =
                let uu____1193 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1193 in
              FStar_Format.parens uu____1192 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1206 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1216 =
                    let uu____1217 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1217 in
                  FStar_Format.parens uu____1216 in
            let name1 = ptsym currentModule name in
            let uu____1219 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1219
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1221,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1233 =
              let uu____1234 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1234 in
            maybe_paren outer t_prio_fun uu____1233
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1235 = FStar_Options.codegen_fsharp () in
            if uu____1235
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1240 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1240
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
            let uu____1294 = FStar_Options.codegen_fsharp () in
            if uu____1294
            then
              let uu____1295 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1] in
              FStar_Format.parens uu____1295
            else
              (let uu____1297 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1297)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs1 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs in
            let uu____1313 = FStar_Format.reduce docs1 in
            FStar_Format.parens uu____1313
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1315 = string_of_mlconstant c in
            FStar_Format.text uu____1315
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1318 = ptsym currentModule path in
            FStar_Format.text uu____1318
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1344 =
              match uu____1344 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1356 =
                    let uu____1359 =
                      let uu____1360 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1360 in
                    [uu____1359; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1356 in
            let uu____1363 =
              let uu____1364 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1364 in
            FStar_Format.cbrackets uu____1363
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1375 = is_standard_constructor ctor in
              if uu____1375
              then
                let uu____1376 =
                  let uu____1381 = as_standard_constructor ctor in
                  FStar_Option.get uu____1381 in
                FStar_Pervasives_Native.snd uu____1376
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1400 = is_standard_constructor ctor in
              if uu____1400
              then
                let uu____1401 =
                  let uu____1406 = as_standard_constructor ctor in
                  FStar_Option.get uu____1406 in
                FStar_Pervasives_Native.snd uu____1401
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1432,uu____1433) ->
                  let uu____1438 =
                    let uu____1441 =
                      let uu____1444 =
                        let uu____1445 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1445 in
                      [uu____1444] in
                    (FStar_Format.text name) :: uu____1441 in
                  FStar_Format.reduce1 uu____1438 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____1455 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1455) es in
            let docs1 =
              let uu____1461 =
                FStar_Format.combine (FStar_Format.text ", ") docs in
              FStar_Format.parens uu____1461 in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1463,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1479 =
                  let uu____1482 =
                    let uu____1485 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1485] in
                  FStar_Format.hardline :: uu____1482 in
                FStar_Format.reduce uu____1479
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1495 =
              let uu____1496 =
                let uu____1499 =
                  let uu____1502 =
                    let uu____1505 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1505] in
                  doc1 :: uu____1502 in
                pre :: uu____1499 in
              FStar_Format.combine FStar_Format.hardline uu____1496 in
            FStar_Format.parens uu____1495
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1515::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1517;
                    FStar_Extraction_ML_Syntax.loc = uu____1518;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1520)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1522;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1523;_}::[])
                 when
                 let uu____1558 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1558 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1581;
                            FStar_Extraction_ML_Syntax.loc = uu____1582;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1584;
                       FStar_Extraction_ML_Syntax.loc = uu____1585;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1641;
                   FStar_Extraction_ML_Syntax.loc = uu____1642;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1655;
                   FStar_Extraction_ML_Syntax.loc = uu____1656;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1663 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1682 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1682)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1691 = FStar_Options.codegen_fsharp () in
              if uu____1691
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1695 =
                   let uu____1698 =
                     let uu____1701 =
                       let uu____1704 =
                         let uu____1705 = ptsym currentModule f in
                         FStar_Format.text uu____1705 in
                       [uu____1704] in
                     (FStar_Format.text ".") :: uu____1701 in
                   e2 :: uu____1698 in
                 FStar_Format.reduce uu____1695) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1731 = FStar_Options.codegen_fsharp () in
              if uu____1731
              then
                let uu____1732 =
                  let uu____1735 =
                    let uu____1738 =
                      let uu____1741 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1743 =
                              let uu____1746 =
                                let uu____1749 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1749] in
                              (FStar_Format.text " : ") :: uu____1746 in
                            FStar_Format.reduce1 uu____1743
                        | uu____1750 -> FStar_Format.text "" in
                      [uu____1741; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1738 in
                  (FStar_Format.text "(") :: uu____1735 in
                FStar_Format.reduce1 uu____1732
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1764  ->
                   match uu____1764 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1777 =
                let uu____1780 =
                  let uu____1783 = FStar_Format.reduce1 ids1 in
                  [uu____1783; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1780 in
              FStar_Format.reduce1 uu____1777 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1794 =
                let uu____1797 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1798 =
                  let uu____1801 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1801; FStar_Format.text "end"] in
                uu____1797 :: uu____1798 in
              FStar_Format.combine FStar_Format.hardline uu____1794 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1817 =
                let uu____1820 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1821 =
                  let uu____1824 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1829 =
                    let uu____1832 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1833 =
                      let uu____1836 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1836; FStar_Format.text "end"] in
                    uu____1832 :: uu____1833 in
                  uu____1824 :: uu____1829 in
                uu____1820 :: uu____1821 in
              FStar_Format.combine FStar_Format.hardline uu____1817 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1874 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1874 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1879 =
              let uu____1882 =
                let uu____1885 =
                  let uu____1886 = ptctor currentModule exn in
                  FStar_Format.text uu____1886 in
                [uu____1885] in
              (FStar_Format.text "raise") :: uu____1882 in
            FStar_Format.reduce1 uu____1879
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1900 =
              let uu____1903 =
                let uu____1906 =
                  let uu____1907 = ptctor currentModule exn in
                  FStar_Format.text uu____1907 in
                let uu____1908 =
                  let uu____1911 =
                    let uu____1912 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1912 in
                  [uu____1911] in
                uu____1906 :: uu____1908 in
              (FStar_Format.text "raise") :: uu____1903 in
            FStar_Format.reduce1 uu____1900
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1935 =
              let uu____1938 =
                let uu____1941 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1946 =
                  let uu____1949 =
                    let uu____1952 =
                      let uu____1953 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1953 in
                    [uu____1952] in
                  (FStar_Format.text "with") :: uu____1949 in
                uu____1941 :: uu____1946 in
              (FStar_Format.text "try") :: uu____1938 in
            FStar_Format.combine FStar_Format.hardline uu____1935
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
          let uu____1966 =
            let uu____1977 = as_bin_op p in FStar_Option.get uu____1977 in
          match uu____1966 with
          | (uu____2000,prio,txt) ->
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
        let uu____2025 =
          let uu____2030 = as_uni_op p in FStar_Option.get uu____2030 in
        match uu____2025 with
        | (uu____2041,txt) ->
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
          let uu____2052 = string_of_mlconstant c in
          FStar_Format.text uu____2052
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2079 =
            match uu____2079 with
            | (name,p) ->
                let uu____2086 =
                  let uu____2089 =
                    let uu____2090 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2090 in
                  let uu____2093 =
                    let uu____2096 =
                      let uu____2099 = doc_of_pattern currentModule p in
                      [uu____2099] in
                    (FStar_Format.text "=") :: uu____2096 in
                  uu____2089 :: uu____2093 in
                FStar_Format.reduce1 uu____2086 in
          let uu____2100 =
            let uu____2101 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2101 in
          FStar_Format.cbrackets uu____2100
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2112 = is_standard_constructor ctor in
            if uu____2112
            then
              let uu____2113 =
                let uu____2118 = as_standard_constructor ctor in
                FStar_Option.get uu____2118 in
              FStar_Pervasives_Native.snd uu____2113
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2137 = is_standard_constructor ctor in
            if uu____2137
            then
              let uu____2138 =
                let uu____2143 = as_standard_constructor ctor in
                FStar_Option.get uu____2143 in
              FStar_Pervasives_Native.snd uu____2138
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2162 =
                  let uu____2165 =
                    let uu____2166 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2166 in
                  let uu____2167 =
                    let uu____2170 =
                      let uu____2173 = doc_of_pattern currentModule xs in
                      [uu____2173] in
                    (FStar_Format.text "::") :: uu____2170 in
                  uu____2165 :: uu____2167 in
                FStar_Format.reduce uu____2162
            | (uu____2174,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2175)::[]) ->
                let uu____2180 =
                  let uu____2183 =
                    let uu____2186 =
                      let uu____2187 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2187 in
                    [uu____2186] in
                  (FStar_Format.text name) :: uu____2183 in
                FStar_Format.reduce1 uu____2180
            | uu____2188 ->
                let uu____2195 =
                  let uu____2198 =
                    let uu____2201 =
                      let uu____2202 =
                        let uu____2203 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2203 in
                      FStar_Format.parens uu____2202 in
                    [uu____2201] in
                  (FStar_Format.text name) :: uu____2198 in
                FStar_Format.reduce1 uu____2195 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2216 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2216
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2227  ->
      match uu____2227 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2236 =
                  let uu____2239 =
                    let uu____2242 = doc_of_pattern currentModule p in
                    [uu____2242] in
                  (FStar_Format.text "|") :: uu____2239 in
                FStar_Format.reduce1 uu____2236
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2249 =
                  let uu____2252 =
                    let uu____2255 = doc_of_pattern currentModule p in
                    [uu____2255; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2252 in
                FStar_Format.reduce1 uu____2249 in
          let uu____2256 =
            let uu____2259 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2260 =
              let uu____2263 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2263; FStar_Format.text "end"] in
            uu____2259 :: uu____2260 in
          FStar_Format.combine FStar_Format.hardline uu____2256
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2269  ->
      match uu____2269 with
      | (rec_,top_level,lets) ->
          let for1 uu____2288 =
            match uu____2288 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2291;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2306 =
                       (FStar_Options.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2306
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2307::uu____2308,uu____2309) ->
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
                                let uu____2361 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu____2361
                                  FStar_Format.reduce1 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "") in
                let uu____2375 =
                  let uu____2378 =
                    let uu____2381 = FStar_Format.reduce1 ids in
                    [uu____2381; ty_annot; FStar_Format.text "="; e1] in
                  (FStar_Format.text name) :: uu____2378 in
                FStar_Format.reduce1 uu____2375 in
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
  fun uu____2395  ->
    match uu____2395 with
    | (lineno,file) ->
        let uu____2398 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Options.codegen_fsharp ()) in
        if uu____2398
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
      let for1 uu____2428 =
        match uu____2428 with
        | (uu____2447,x,mangle_opt,tparams,uu____2451,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2469 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams in
                  let uu____2477 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2477 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2501 =
                    match uu____2501 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2514 =
                    let uu____2515 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2515 in
                  FStar_Format.cbrackets uu____2514
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2548 =
                    match uu____2548 with
                    | (name,tys) ->
                        let uu____2573 = FStar_List.split tys in
                        (match uu____2573 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2592 ->
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
              let uu____2622 =
                let uu____2625 =
                  let uu____2628 =
                    let uu____2629 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2629 in
                  [uu____2628] in
                tparams1 :: uu____2625 in
              FStar_Format.reduce1 uu____2622 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2634 =
                   let uu____2637 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2637; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2634) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2660 =
            let uu____2663 =
              let uu____2666 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2666] in
            (FStar_Format.text "type") :: uu____2663 in
          FStar_Format.reduce1 uu____2660
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
          let uu____2684 =
            let uu____2687 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____2688 =
              let uu____2691 = doc_of_sig currentModule subsig in
              let uu____2692 =
                let uu____2695 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____2695] in
              uu____2691 :: uu____2692 in
            uu____2687 :: uu____2688 in
          FStar_Format.combine FStar_Format.hardline uu____2684
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____2713 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____2713 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2715,ty)) ->
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
            let uu____2783 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____2783 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____2786,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____2795 =
            let uu____2798 =
              let uu____2801 =
                let uu____2804 =
                  let uu____2807 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____2807] in
                (FStar_Format.text "=") :: uu____2804 in
              (FStar_Format.text "_") :: uu____2801 in
            (FStar_Format.text "let") :: uu____2798 in
          FStar_Format.reduce1 uu____2795
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2831 ->
                  FStar_Format.empty
              | uu____2832 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2841  ->
    match uu____2841 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2907 =
          match uu____2907 with
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
                  (fun uu____2980  ->
                     match uu____2980 with
                     | (s,uu____2986) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____3013 =
                let uu____3016 =
                  let uu____3019 =
                    let uu____3022 = FStar_Format.reduce sub3 in
                    [uu____3022;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3019 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3016 in
              FStar_Format.reduce uu____3013
        and for1_mod istop uu____3025 =
          match uu____3025 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1 in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3093 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3104 =
                  let uu____3107 = FStar_Options.codegen_fsharp () in
                  if uu____3107
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
                FStar_Format.reduce1 uu____3104 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3126  ->
                     match uu____3126 with
                     | (uu____3131,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3162 = FStar_Options.codegen_fsharp () in
                if uu____3162
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3166 =
                let uu____3169 =
                  let uu____3172 =
                    let uu____3175 =
                      let uu____3178 =
                        let uu____3181 =
                          let uu____3184 = FStar_Format.reduce sub3 in
                          [uu____3184;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3181 in
                      FStar_Format.hardline :: uu____3178 in
                    FStar_List.append maybe_open_pervasives uu____3175 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3172 in
                FStar_List.append prefix1 uu____3169 in
              FStar_All.pipe_left FStar_Format.reduce uu____3166 in
        let docs =
          FStar_List.map
            (fun uu____3223  ->
               match uu____3223 with
               | (x,s,m) ->
                   let uu____3273 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3274 = for1_mod true (x, s, m) in
                   (uu____3273, uu____3274)) mllib in
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
        let uu____3303 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3303 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3315 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3315 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1