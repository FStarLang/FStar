open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
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
  | Infix of assoc
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
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
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
      let uu____337 = FStar_String.get s (Prims.parse_int "0") in
      uu____335 <> uu____337 in
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
        (let uu____352 = mlpath_of_mlpath currentModule mlp in
         match uu____352 with
         | (p,s) ->
             let uu____359 =
               let uu____362 =
                 let uu____365 = ptsym_of_symbol s in [uu____365] in
               FStar_List.append p uu____362 in
             FStar_String.concat "." uu____359)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____374 = mlpath_of_mlpath currentModule mlp in
      match uu____374 with
      | (p,s) ->
          let s1 =
            let uu____382 =
              let uu____383 =
                let uu____384 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____384 in
              let uu____385 = FStar_String.get s (Prims.parse_int "0") in
              uu____383 <> uu____385 in
            if uu____382 then Prims.strcat "U__" s else s in
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
let prim_types: 'Auu____629 . Prims.unit -> 'Auu____629 Prims.list =
  fun uu____632  -> []
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
  fun uu____684  ->
    match uu____684 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____729  ->
               match uu____729 with | (y,uu____741,uu____742) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____766 = as_bin_op p in uu____766 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____810  ->
    match uu____810 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____836  -> match uu____836 with | (y,uu____842) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____852 = as_uni_op p in uu____852 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____882  ->
    match uu____882 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____908  -> match uu____908 with | (y,uu____914) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____924 = as_standard_constructor p in
    uu____924 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____962  ->
    fun inner  ->
      fun doc1  ->
        match uu____962 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1013 = _inner in
              match uu____1013 with
              | (pi,fi) ->
                  let uu____1020 = _outer in
                  (match uu____1020 with
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
                           | (uu____1027,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1028,uu____1029) -> false))) in
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
    fun uu___127_1049  ->
      match uu___127_1049 with
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
        let uu____1070 = FStar_Util.string_of_int nc in
        Prims.strcat uu____1070
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
        (s,FStar_Pervasives_Native.Some (uu____1139,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1151,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1177 =
          let uu____1178 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1178 "\"" in
        Prims.strcat "\"" uu____1177
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1180 =
          let uu____1181 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1181 "\"" in
        Prims.strcat "\"" uu____1180
    | uu____1182 ->
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
              let uu____1215 =
                let uu____1216 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1216 in
              FStar_Format.parens uu____1215 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1229 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1239 =
                    let uu____1240 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1240 in
                  FStar_Format.parens uu____1239 in
            let name1 = ptsym currentModule name in
            let uu____1242 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1242
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1244,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1256 =
              let uu____1257 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1257 in
            maybe_paren outer t_prio_fun uu____1256
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1258 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1258
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1263 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1263
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
            let uu____1317 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1317
            then
              let uu____1318 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____1318
            else
              (let uu____1320 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1320)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____1336 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____1336
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1338 = string_of_mlconstant c in
            FStar_Format.text uu____1338
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1341 = ptsym currentModule path in
            FStar_Format.text uu____1341
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1367 =
              match uu____1367 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1379 =
                    let uu____1382 =
                      let uu____1383 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1383 in
                    [uu____1382; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1379 in
            let uu____1386 =
              let uu____1387 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1387 in
            FStar_Format.cbrackets uu____1386
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1398 = is_standard_constructor ctor in
              if uu____1398
              then
                let uu____1399 =
                  let uu____1404 = as_standard_constructor ctor in
                  FStar_Option.get uu____1404 in
                FStar_Pervasives_Native.snd uu____1399
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1423 = is_standard_constructor ctor in
              if uu____1423
              then
                let uu____1424 =
                  let uu____1429 = as_standard_constructor ctor in
                  FStar_Option.get uu____1429 in
                FStar_Pervasives_Native.snd uu____1424
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1455,uu____1456) ->
                  let uu____1461 =
                    let uu____1464 =
                      let uu____1467 =
                        let uu____1468 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1468 in
                      [uu____1467] in
                    (FStar_Format.text name) :: uu____1464 in
                  FStar_Format.reduce1 uu____1461 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____1478 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1478) es in
            let docs2 =
              let uu____1484 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____1484 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1486,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1502 =
                  let uu____1505 =
                    let uu____1508 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1508] in
                  FStar_Format.hardline :: uu____1505 in
                FStar_Format.reduce uu____1502
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1518 =
              let uu____1519 =
                let uu____1522 =
                  let uu____1525 =
                    let uu____1528 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1528] in
                  doc1 :: uu____1525 in
                pre :: uu____1522 in
              FStar_Format.combine FStar_Format.hardline uu____1519 in
            FStar_Format.parens uu____1518
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1538::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1540;
                    FStar_Extraction_ML_Syntax.loc = uu____1541;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1543)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1545;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1546;_}::[])
                 when
                 let uu____1581 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1581 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1604;
                            FStar_Extraction_ML_Syntax.loc = uu____1605;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1607;
                       FStar_Extraction_ML_Syntax.loc = uu____1608;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1664;
                   FStar_Extraction_ML_Syntax.loc = uu____1665;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1678;
                   FStar_Extraction_ML_Syntax.loc = uu____1679;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1686 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1705 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1705)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1714 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1714
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1718 =
                   let uu____1721 =
                     let uu____1724 =
                       let uu____1727 =
                         let uu____1728 = ptsym currentModule f in
                         FStar_Format.text uu____1728 in
                       [uu____1727] in
                     (FStar_Format.text ".") :: uu____1724 in
                   e2 :: uu____1721 in
                 FStar_Format.reduce uu____1718) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1754 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1754
              then
                let uu____1755 =
                  let uu____1758 =
                    let uu____1761 =
                      let uu____1764 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1766 =
                              let uu____1769 =
                                let uu____1772 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1772] in
                              (FStar_Format.text " : ") :: uu____1769 in
                            FStar_Format.reduce1 uu____1766
                        | uu____1773 -> FStar_Format.text "" in
                      [uu____1764; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1761 in
                  (FStar_Format.text "(") :: uu____1758 in
                FStar_Format.reduce1 uu____1755
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1787  ->
                   match uu____1787 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1800 =
                let uu____1803 =
                  let uu____1806 = FStar_Format.reduce1 ids1 in
                  [uu____1806; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1803 in
              FStar_Format.reduce1 uu____1800 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
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
                  [uu____1824; FStar_Format.text "end"] in
                uu____1820 :: uu____1821 in
              FStar_Format.combine FStar_Format.hardline uu____1817 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1840 =
                let uu____1843 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1844 =
                  let uu____1847 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1852 =
                    let uu____1855 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1856 =
                      let uu____1859 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1859; FStar_Format.text "end"] in
                    uu____1855 :: uu____1856 in
                  uu____1847 :: uu____1852 in
                uu____1843 :: uu____1844 in
              FStar_Format.combine FStar_Format.hardline uu____1840 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1897 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1897 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1902 =
              let uu____1905 =
                let uu____1908 =
                  let uu____1909 = ptctor currentModule exn in
                  FStar_Format.text uu____1909 in
                [uu____1908] in
              (FStar_Format.text "raise") :: uu____1905 in
            FStar_Format.reduce1 uu____1902
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1923 =
              let uu____1926 =
                let uu____1929 =
                  let uu____1930 = ptctor currentModule exn in
                  FStar_Format.text uu____1930 in
                let uu____1931 =
                  let uu____1934 =
                    let uu____1935 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1935 in
                  [uu____1934] in
                uu____1929 :: uu____1931 in
              (FStar_Format.text "raise") :: uu____1926 in
            FStar_Format.reduce1 uu____1923
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1958 =
              let uu____1961 =
                let uu____1964 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1969 =
                  let uu____1972 =
                    let uu____1975 =
                      let uu____1976 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1976 in
                    [uu____1975] in
                  (FStar_Format.text "with") :: uu____1972 in
                uu____1964 :: uu____1969 in
              (FStar_Format.text "try") :: uu____1961 in
            FStar_Format.combine FStar_Format.hardline uu____1958
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
          let uu____1983 =
            let uu____1994 = as_bin_op p in FStar_Option.get uu____1994 in
          match uu____1983 with
          | (uu____2017,prio,txt) ->
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
        let uu____2042 =
          let uu____2047 = as_uni_op p in FStar_Option.get uu____2047 in
        match uu____2042 with
        | (uu____2058,txt) ->
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
          let uu____2069 = string_of_mlconstant c in
          FStar_Format.text uu____2069
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2096 =
            match uu____2096 with
            | (name,p) ->
                let uu____2103 =
                  let uu____2106 =
                    let uu____2107 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2107 in
                  let uu____2110 =
                    let uu____2113 =
                      let uu____2116 = doc_of_pattern currentModule p in
                      [uu____2116] in
                    (FStar_Format.text "=") :: uu____2113 in
                  uu____2106 :: uu____2110 in
                FStar_Format.reduce1 uu____2103 in
          let uu____2117 =
            let uu____2118 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2118 in
          FStar_Format.cbrackets uu____2117
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2129 = is_standard_constructor ctor in
            if uu____2129
            then
              let uu____2130 =
                let uu____2135 = as_standard_constructor ctor in
                FStar_Option.get uu____2135 in
              FStar_Pervasives_Native.snd uu____2130
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2154 = is_standard_constructor ctor in
            if uu____2154
            then
              let uu____2155 =
                let uu____2160 = as_standard_constructor ctor in
                FStar_Option.get uu____2160 in
              FStar_Pervasives_Native.snd uu____2155
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2179 =
                  let uu____2182 =
                    let uu____2183 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2183 in
                  let uu____2184 =
                    let uu____2187 =
                      let uu____2190 = doc_of_pattern currentModule xs in
                      [uu____2190] in
                    (FStar_Format.text "::") :: uu____2187 in
                  uu____2182 :: uu____2184 in
                FStar_Format.reduce uu____2179
            | (uu____2191,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2192)::[]) ->
                let uu____2197 =
                  let uu____2200 =
                    let uu____2203 =
                      let uu____2204 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2204 in
                    [uu____2203] in
                  (FStar_Format.text name) :: uu____2200 in
                FStar_Format.reduce1 uu____2197
            | uu____2205 ->
                let uu____2212 =
                  let uu____2215 =
                    let uu____2218 =
                      let uu____2219 =
                        let uu____2220 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2220 in
                      FStar_Format.parens uu____2219 in
                    [uu____2218] in
                  (FStar_Format.text name) :: uu____2215 in
                FStar_Format.reduce1 uu____2212 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2233 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2233
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2244  ->
      match uu____2244 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2253 =
                  let uu____2256 =
                    let uu____2259 = doc_of_pattern currentModule p in
                    [uu____2259] in
                  (FStar_Format.text "|") :: uu____2256 in
                FStar_Format.reduce1 uu____2253
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2266 =
                  let uu____2269 =
                    let uu____2272 = doc_of_pattern currentModule p in
                    [uu____2272; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2269 in
                FStar_Format.reduce1 uu____2266 in
          let uu____2273 =
            let uu____2276 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2277 =
              let uu____2280 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2280; FStar_Format.text "end"] in
            uu____2276 :: uu____2277 in
          FStar_Format.combine FStar_Format.hardline uu____2273
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2286  ->
      match uu____2286 with
      | (rec_,top_level,lets) ->
          let for1 uu____2305 =
            match uu____2305 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2308;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2323 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2323
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2324::uu____2325,uu____2326) ->
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
                                let uu____2378 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu____2378
                                  FStar_Format.reduce1 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "") in
                let uu____2392 =
                  let uu____2395 =
                    let uu____2398 = FStar_Format.reduce1 ids in
                    [uu____2398; ty_annot; FStar_Format.text "="; e1] in
                  (FStar_Format.text name) :: uu____2395 in
                FStar_Format.reduce1 uu____2392 in
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
  fun uu____2412  ->
    match uu____2412 with
    | (lineno,file) ->
        let uu____2415 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____2415
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
      let for1 uu____2447 =
        match uu____2447 with
        | (uu____2466,x,mangle_opt,tparams,uu____2470,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2488 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams in
                  let uu____2496 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2496 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2520 =
                    match uu____2520 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2533 =
                    let uu____2534 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2534 in
                  FStar_Format.cbrackets uu____2533
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2567 =
                    match uu____2567 with
                    | (name,tys) ->
                        let uu____2592 = FStar_List.split tys in
                        (match uu____2592 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2611 ->
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
              let uu____2641 =
                let uu____2644 =
                  let uu____2647 =
                    let uu____2648 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2648 in
                  [uu____2647] in
                tparams1 :: uu____2644 in
              FStar_Format.reduce1 uu____2641 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2653 =
                   let uu____2656 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2656; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2653) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2679 =
            let uu____2682 =
              let uu____2685 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2685] in
            (FStar_Format.text "type") :: uu____2682 in
          FStar_Format.reduce1 uu____2679
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
          let uu____2703 =
            let uu____2706 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____2707 =
              let uu____2710 = doc_of_sig currentModule subsig in
              let uu____2711 =
                let uu____2714 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____2714] in
              uu____2710 :: uu____2711 in
            uu____2706 :: uu____2707 in
          FStar_Format.combine FStar_Format.hardline uu____2703
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____2732 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____2732 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2734,ty)) ->
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
            let uu____2804 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____2804 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____2807,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____2816 =
            let uu____2819 =
              let uu____2822 =
                let uu____2825 =
                  let uu____2828 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____2828] in
                (FStar_Format.text "=") :: uu____2825 in
              (FStar_Format.text "_") :: uu____2822 in
            (FStar_Format.text "let") :: uu____2819 in
          FStar_Format.reduce1 uu____2816
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2854 ->
                  FStar_Format.empty
              | uu____2855 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2865  ->
    match uu____2865 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2931 =
          match uu____2931 with
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
                  (fun uu____3004  ->
                     match uu____3004 with
                     | (s,uu____3010) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____3037 =
                let uu____3040 =
                  let uu____3043 =
                    let uu____3046 = FStar_Format.reduce sub3 in
                    [uu____3046;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3043 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3040 in
              FStar_Format.reduce uu____3037
        and for1_mod istop uu____3049 =
          match uu____3049 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3117 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3128 =
                  let uu____3131 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____3131
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
                FStar_Format.reduce1 uu____3128 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3150  ->
                     match uu____3150 with
                     | (uu____3155,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3186 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____3186
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3190 =
                let uu____3193 =
                  let uu____3196 =
                    let uu____3199 =
                      let uu____3202 =
                        let uu____3205 =
                          let uu____3208 = FStar_Format.reduce sub3 in
                          [uu____3208;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3205 in
                      FStar_Format.hardline :: uu____3202 in
                    FStar_List.append maybe_open_pervasives uu____3199 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3196 in
                FStar_List.append prefix1 uu____3193 in
              FStar_All.pipe_left FStar_Format.reduce uu____3190 in
        let docs1 =
          FStar_List.map
            (fun uu____3247  ->
               match uu____3247 with
               | (x,s,m) ->
                   let uu____3297 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3298 = for1_mod true (x, s, m) in
                   (uu____3297, uu____3298)) mllib in
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
        let uu____3330 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3330 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3344 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3344 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1