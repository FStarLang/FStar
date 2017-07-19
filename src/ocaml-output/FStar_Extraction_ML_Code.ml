open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
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
  | Infix of assoc
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
let rec in_ns x =
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
                  let uu____226 = FStar_Util.first_N cg_len ns in
                  match uu____226 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____257 =
                           let uu____260 =
                             let uu____263 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____263] in
                           FStar_List.append pfx uu____260 in
                         FStar_Pervasives_Native.Some uu____257
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
      let uu____287 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____287 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____292 ->
          let uu____293 = x in
          (match uu____293 with
           | (ns,x1) ->
               let uu____300 = path_of_ns currentModule ns in (uu____300, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____308 =
      let uu____309 =
        let uu____310 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____310 in
      let uu____311 = FStar_String.get s (Prims.parse_int "0") in
      uu____309 <> uu____311 in
    if uu____308 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____324 = mlpath_of_mlpath currentModule mlp in
         match uu____324 with
         | (p,s) ->
             let uu____331 =
               let uu____334 =
                 let uu____337 = ptsym_of_symbol s in [uu____337] in
               FStar_List.append p uu____334 in
             FStar_String.concat "." uu____331)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____344 = mlpath_of_mlpath currentModule mlp in
      match uu____344 with
      | (p,s) ->
          let s1 =
            let uu____352 =
              let uu____353 =
                let uu____354 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____354 in
              let uu____355 = FStar_String.get s (Prims.parse_int "0") in
              uu____353 <> uu____355 in
            if uu____352 then Prims.strcat "U__" s else s in
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
let prim_types uu____601 = []
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
  fun uu____651  ->
    match uu____651 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____692  ->
               match uu____692 with | (y,uu____704,uu____705) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____728 = as_bin_op p in uu____728 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____771  ->
    match uu____771 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____794  -> match uu____794 with | (y,uu____800) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____809 = as_uni_op p in uu____809 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____837  ->
    match uu____837 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____860  -> match uu____860 with | (y,uu____866) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____875 = as_standard_constructor p in
    uu____875 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____910  ->
    fun inner  ->
      fun doc1  ->
        match uu____910 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____961 = _inner in
              match uu____961 with
              | (pi,fi) ->
                  let uu____968 = _outer in
                  (match uu____968 with
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
                           | (uu____975,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____976,uu____977) -> false))) in
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
    fun uu___118_993  ->
      match uu___118_993 with
      | c when c = '\\' -> "\\\\"
      | c when c = ' ' -> " "
      | c when c = '\b' -> "\\b"
      | c when c = '\t' -> "\\t"
      | c when c = '\r' -> "\\r"
      | c when c = '\n' -> "\\n"
      | c when c = '\'' -> "\\'"
      | c when c = '"' -> "\\\""
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
        let uu____1012 =
          let uu____1013 = escape_or escape_char_hex c in
          Prims.strcat uu____1013 "'" in
        Prims.strcat "'" uu____1012
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1037,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1049,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1075 =
          let uu____1076 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1076 "\"" in
        Prims.strcat "\"" uu____1075
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1078 =
          let uu____1079 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1079 "\"" in
        Prims.strcat "\"" uu____1078
    | uu____1080 ->
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
              then FStar_Util.replace_char s '_' 'u'
              else s in
            let uu____1102 =
              let uu____1103 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____1103 in
            FStar_Format.text uu____1102
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____1115 =
                let uu____1116 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1116 in
              FStar_Format.parens uu____1115 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1129 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1139 =
                    let uu____1140 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1140 in
                  FStar_Format.parens uu____1139 in
            let name1 = ptsym currentModule name in
            let uu____1142 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1142
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1144,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1156 =
              let uu____1157 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1157 in
            maybe_paren outer t_prio_fun uu____1156
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1158 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1158
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1163 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1163
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
            let uu____1217 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1217
            then
              let uu____1218 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____1218
            else
              (let uu____1220 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1220)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____1235 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____1235
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1237 = string_of_mlconstant c in
            FStar_Format.text uu____1237
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____1239) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1241 = ptsym currentModule path in
            FStar_Format.text uu____1241
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1267 =
              match uu____1267 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1279 =
                    let uu____1282 =
                      let uu____1283 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1283 in
                    [uu____1282; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1279 in
            let uu____1286 =
              let uu____1287 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1287 in
            FStar_Format.cbrackets uu____1286
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1298 = is_standard_constructor ctor in
              if uu____1298
              then
                let uu____1299 =
                  let uu____1304 = as_standard_constructor ctor in
                  FStar_Option.get uu____1304 in
                FStar_Pervasives_Native.snd uu____1299
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1323 = is_standard_constructor ctor in
              if uu____1323
              then
                let uu____1324 =
                  let uu____1329 = as_standard_constructor ctor in
                  FStar_Option.get uu____1329 in
                FStar_Pervasives_Native.snd uu____1324
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1355,uu____1356) ->
                  let uu____1361 =
                    let uu____1364 =
                      let uu____1367 =
                        let uu____1368 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1368 in
                      [uu____1367] in
                    (FStar_Format.text name) :: uu____1364 in
                  FStar_Format.reduce1 uu____1361 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____1376 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1376) es in
            let docs2 =
              let uu____1382 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____1382 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1384,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1400 =
                  let uu____1403 =
                    let uu____1406 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1406] in
                  FStar_Format.hardline :: uu____1403 in
                FStar_Format.reduce uu____1400
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1416 =
              let uu____1417 =
                let uu____1420 =
                  let uu____1423 =
                    let uu____1426 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1426] in
                  doc1 :: uu____1423 in
                pre :: uu____1420 in
              FStar_Format.combine FStar_Format.hardline uu____1417 in
            FStar_Format.parens uu____1416
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1436::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1438;
                    FStar_Extraction_ML_Syntax.loc = uu____1439;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1441)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1443;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1444;_}::[])
                 when
                 let uu____1479 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1479 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1502;
                            FStar_Extraction_ML_Syntax.loc = uu____1503;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1505;
                       FStar_Extraction_ML_Syntax.loc = uu____1506;_} when
                       let uu____1527 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1528 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1527 = uu____1528 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1564;
                   FStar_Extraction_ML_Syntax.loc = uu____1565;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1578;
                   FStar_Extraction_ML_Syntax.loc = uu____1579;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1586 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1605 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1605)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1614 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1614
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1618 =
                   let uu____1621 =
                     let uu____1624 =
                       let uu____1627 =
                         let uu____1628 = ptsym currentModule f in
                         FStar_Format.text uu____1628 in
                       [uu____1627] in
                     (FStar_Format.text ".") :: uu____1624 in
                   e2 :: uu____1621 in
                 FStar_Format.reduce uu____1618) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1654 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1654
              then
                let uu____1655 =
                  let uu____1658 =
                    let uu____1661 =
                      let uu____1664 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1666 =
                              let uu____1669 =
                                let uu____1672 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1672] in
                              (FStar_Format.text " : ") :: uu____1669 in
                            FStar_Format.reduce1 uu____1666
                        | uu____1673 -> FStar_Format.text "" in
                      [uu____1664; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1661 in
                  (FStar_Format.text "(") :: uu____1658 in
                FStar_Format.reduce1 uu____1655
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1688  ->
                   match uu____1688 with
                   | ((x,uu____1698),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1710 =
                let uu____1713 =
                  let uu____1716 = FStar_Format.reduce1 ids1 in
                  [uu____1716; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1713 in
              FStar_Format.reduce1 uu____1710 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1727 =
                let uu____1730 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1731 =
                  let uu____1734 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1734; FStar_Format.text "end"] in
                uu____1730 :: uu____1731 in
              FStar_Format.combine FStar_Format.hardline uu____1727 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1750 =
                let uu____1753 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1754 =
                  let uu____1757 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1762 =
                    let uu____1765 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1766 =
                      let uu____1769 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1769; FStar_Format.text "end"] in
                    uu____1765 :: uu____1766 in
                  uu____1757 :: uu____1762 in
                uu____1753 :: uu____1754 in
              FStar_Format.combine FStar_Format.hardline uu____1750 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1807 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1807 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1812 =
              let uu____1815 =
                let uu____1818 =
                  let uu____1819 = ptctor currentModule exn in
                  FStar_Format.text uu____1819 in
                [uu____1818] in
              (FStar_Format.text "raise") :: uu____1815 in
            FStar_Format.reduce1 uu____1812
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1833 =
              let uu____1836 =
                let uu____1839 =
                  let uu____1840 = ptctor currentModule exn in
                  FStar_Format.text uu____1840 in
                let uu____1841 =
                  let uu____1844 =
                    let uu____1845 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1845 in
                  [uu____1844] in
                uu____1839 :: uu____1841 in
              (FStar_Format.text "raise") :: uu____1836 in
            FStar_Format.reduce1 uu____1833
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1868 =
              let uu____1871 =
                let uu____1874 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1879 =
                  let uu____1882 =
                    let uu____1885 =
                      let uu____1886 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1886 in
                    [uu____1885] in
                  (FStar_Format.text "with") :: uu____1882 in
                uu____1874 :: uu____1879 in
              (FStar_Format.text "try") :: uu____1871 in
            FStar_Format.combine FStar_Format.hardline uu____1868
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
          let uu____1893 =
            let uu____1904 = as_bin_op p in FStar_Option.get uu____1904 in
          match uu____1893 with
          | (uu____1927,prio,txt) ->
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
        let uu____1952 =
          let uu____1957 = as_uni_op p in FStar_Option.get uu____1957 in
        match uu____1952 with
        | (uu____1968,txt) ->
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
          let uu____1979 = string_of_mlconstant c in
          FStar_Format.text uu____1979
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2006 =
            match uu____2006 with
            | (name,p) ->
                let uu____2013 =
                  let uu____2016 =
                    let uu____2017 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2017 in
                  let uu____2020 =
                    let uu____2023 =
                      let uu____2026 = doc_of_pattern currentModule p in
                      [uu____2026] in
                    (FStar_Format.text "=") :: uu____2023 in
                  uu____2016 :: uu____2020 in
                FStar_Format.reduce1 uu____2013 in
          let uu____2027 =
            let uu____2028 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2028 in
          FStar_Format.cbrackets uu____2027
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2039 = is_standard_constructor ctor in
            if uu____2039
            then
              let uu____2040 =
                let uu____2045 = as_standard_constructor ctor in
                FStar_Option.get uu____2045 in
              FStar_Pervasives_Native.snd uu____2040
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2064 = is_standard_constructor ctor in
            if uu____2064
            then
              let uu____2065 =
                let uu____2070 = as_standard_constructor ctor in
                FStar_Option.get uu____2070 in
              FStar_Pervasives_Native.snd uu____2065
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2089 =
                  let uu____2092 =
                    let uu____2093 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2093 in
                  let uu____2094 =
                    let uu____2097 =
                      let uu____2100 = doc_of_pattern currentModule xs in
                      [uu____2100] in
                    (FStar_Format.text "::") :: uu____2097 in
                  uu____2092 :: uu____2094 in
                FStar_Format.reduce uu____2089
            | (uu____2101,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2102)::[]) ->
                let uu____2107 =
                  let uu____2110 =
                    let uu____2113 =
                      let uu____2114 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2114 in
                    [uu____2113] in
                  (FStar_Format.text name) :: uu____2110 in
                FStar_Format.reduce1 uu____2107
            | uu____2115 ->
                let uu____2122 =
                  let uu____2125 =
                    let uu____2128 =
                      let uu____2129 =
                        let uu____2130 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2130 in
                      FStar_Format.parens uu____2129 in
                    [uu____2128] in
                  (FStar_Format.text name) :: uu____2125 in
                FStar_Format.reduce1 uu____2122 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2143 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2143
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2154  ->
      match uu____2154 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2163 =
                  let uu____2166 =
                    let uu____2169 = doc_of_pattern currentModule p in
                    [uu____2169] in
                  (FStar_Format.text "|") :: uu____2166 in
                FStar_Format.reduce1 uu____2163
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2176 =
                  let uu____2179 =
                    let uu____2182 = doc_of_pattern currentModule p in
                    [uu____2182; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2179 in
                FStar_Format.reduce1 uu____2176 in
          let uu____2183 =
            let uu____2186 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2187 =
              let uu____2190 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2190; FStar_Format.text "end"] in
            uu____2186 :: uu____2187 in
          FStar_Format.combine FStar_Format.hardline uu____2183
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2196  ->
      match uu____2196 with
      | (rec_,top_level,lets) ->
          let for1 uu____2215 =
            match uu____2215 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2218;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2233 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2233
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2234::uu____2235,uu____2236) ->
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
                          | FStar_Pervasives_Native.Some
                              (uu____2262::uu____2263,uu____2264) ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____2290 =
                  let uu____2293 =
                    let uu____2294 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____2294 in
                  let uu____2295 =
                    let uu____2298 = FStar_Format.reduce1 ids in
                    [uu____2298; ty_annot; FStar_Format.text "="; e1] in
                  uu____2293 :: uu____2295 in
                FStar_Format.reduce1 uu____2290 in
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
  fun uu____2310  ->
    match uu____2310 with
    | (lineno,file) ->
        let uu____2313 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____2313
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
      let for1 uu____2341 =
        match uu____2341 with
        | (uu____2358,x,mangle_opt,tparams,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____2379 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____2379
              | uu____2380 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____2387 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____2387) tparams in
                  let uu____2388 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2388 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2412 =
                    match uu____2412 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2425 =
                    let uu____2426 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2426 in
                  FStar_Format.cbrackets uu____2425
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2459 =
                    match uu____2459 with
                    | (name,tys) ->
                        let uu____2484 = FStar_List.split tys in
                        (match uu____2484 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2503 ->
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
              let uu____2532 =
                let uu____2535 =
                  let uu____2538 =
                    let uu____2539 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2539 in
                  [uu____2538] in
                tparams1 :: uu____2535 in
              FStar_Format.reduce1 uu____2532 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2544 =
                   let uu____2547 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2547; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2544) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2568 =
            let uu____2571 =
              let uu____2574 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2574] in
            (FStar_Format.text "type") :: uu____2571 in
          FStar_Format.reduce1 uu____2568
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
          let uu____2592 =
            let uu____2595 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____2596 =
              let uu____2599 = doc_of_sig currentModule subsig in
              let uu____2600 =
                let uu____2603 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____2603] in
              uu____2599 :: uu____2600 in
            uu____2595 :: uu____2596 in
          FStar_Format.combine FStar_Format.hardline uu____2592
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____2621 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____2621 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2623,ty)) ->
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
            let uu____2690 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____2690 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____2693,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____2702 =
            let uu____2705 =
              let uu____2708 =
                let uu____2711 =
                  let uu____2714 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____2714] in
                (FStar_Format.text "=") :: uu____2711 in
              (FStar_Format.text "_") :: uu____2708 in
            (FStar_Format.text "let") :: uu____2705 in
          FStar_Format.reduce1 uu____2702
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2735 ->
                  FStar_Format.empty
              | uu____2736 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2745  ->
    match uu____2745 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2811 =
          match uu____2811 with
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
                  (fun uu____2881  ->
                     match uu____2881 with
                     | (s,uu____2887) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____2913 =
                let uu____2916 =
                  let uu____2919 =
                    let uu____2922 = FStar_Format.reduce sub3 in
                    [uu____2922;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____2919 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____2916 in
              FStar_Format.reduce uu____2913
        and for1_mod istop uu____2925 =
          match uu____2925 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____2993 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3004 =
                  let uu____3007 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____3007
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
                FStar_Format.reduce1 uu____3004 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3023  ->
                     match uu____3023 with
                     | (uu____3028,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3058 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____3058
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3062 =
                let uu____3065 =
                  let uu____3068 =
                    let uu____3071 =
                      let uu____3074 =
                        let uu____3077 =
                          let uu____3080 = FStar_Format.reduce sub3 in
                          [uu____3080;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3077 in
                      FStar_Format.hardline :: uu____3074 in
                    FStar_List.append maybe_open_pervasives uu____3071 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3068 in
                FStar_List.append prefix1 uu____3065 in
              FStar_All.pipe_left FStar_Format.reduce uu____3062 in
        let docs1 =
          FStar_List.map
            (fun uu____3113  ->
               match uu____3113 with
               | (x,s,m) ->
                   let uu____3163 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3164 = for1_mod true (x, s, m) in
                   (uu____3163, uu____3164)) mllib in
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
        let uu____3193 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3193 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3205 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3205 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1