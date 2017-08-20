open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
let (uu___is_ILeft :assoc -> Prims.bool)=
  fun projectee  -> match projectee with | ILeft  -> true | uu____5 -> false
let (uu___is_IRight :assoc -> Prims.bool)=
  fun projectee  ->
    match projectee with | IRight  -> true | uu____10 -> false
let (uu___is_Left :assoc -> Prims.bool)=
  fun projectee  -> match projectee with | Left  -> true | uu____15 -> false
let (uu___is_Right :assoc -> Prims.bool)=
  fun projectee  -> match projectee with | Right  -> true | uu____20 -> false
let (uu___is_NonAssoc :assoc -> Prims.bool)=
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____25 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc
let (uu___is_Prefix :fixity -> Prims.bool)=
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____34 -> false
let (uu___is_Postfix :fixity -> Prims.bool)=
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____39 -> false
let (uu___is_Infix :fixity -> Prims.bool)=
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____45 -> false
let (__proj__Infix__item___0 :fixity -> assoc)=
  fun projectee  -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
let (t_prio_fun :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "10"), (Infix Right))
let (t_prio_tpl :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "20"), (Infix NonAssoc))
let (t_prio_name :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "30"), Postfix)
let (e_bin_prio_lambda :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "5"), Prefix)
let (e_bin_prio_if :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "15"), Prefix)
let (e_bin_prio_letin :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "19"), Prefix)
let (e_bin_prio_or :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "20"), (Infix Left))
let (e_bin_prio_and :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "25"), (Infix Left))
let (e_bin_prio_eq :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "27"), (Infix NonAssoc))
let (e_bin_prio_order :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "29"), (Infix NonAssoc))
let (e_bin_prio_op1 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "30"), (Infix Left))
let (e_bin_prio_op2 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "40"), (Infix Left))
let (e_bin_prio_op3 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "50"), (Infix Left))
let (e_bin_prio_op4 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "60"), (Infix Left))
let (e_bin_prio_comb :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "70"), (Infix Left))
let (e_bin_prio_seq :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "100"), (Infix Left))
let (e_app_prio :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "10000"), (Infix Left))
let (min_op_prec :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let (max_op_prec :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  (FStar_Util.max_int, (Infix NonAssoc))
let rec in_ns :
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool=
  fun x  ->
    match x with
    | ([],uu____164) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____187,uu____188) -> false
let (path_of_ns
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     Prims.string Prims.list -> Prims.string Prims.list)=
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
                  let uu____248 = FStar_Util.first_N cg_len ns in
                  match uu____248 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____281 =
                           let uu____284 =
                             let uu____287 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____287] in
                           FStar_List.append pfx uu____284 in
                         FStar_Pervasives_Native.Some uu____281
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None) in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
let (mlpath_of_mlpath
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath)=
  fun currentModule  ->
    fun x  ->
      let uu____313 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____313 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____318 ->
          let uu____319 = x in
          (match uu____319 with
           | (ns,x1) ->
               let uu____326 = path_of_ns currentModule ns in (uu____326, x1))
let (ptsym_of_symbol
  :FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)=
  fun s  ->
    let uu____335 =
      let uu____336 =
        let uu____337 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____337 in
      let uu____338 = FStar_String.get s (Prims.parse_int "0") in
      uu____336 <> uu____338 in
    if uu____335 then Prims.strcat "l__" s else s
let (ptsym
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)=
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____353 = mlpath_of_mlpath currentModule mlp in
         match uu____353 with
         | (p,s) ->
             let uu____360 =
               let uu____363 =
                 let uu____366 = ptsym_of_symbol s in [uu____366] in
               FStar_List.append p uu____363 in
             FStar_String.concat "." uu____360)
let (ptctor
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)=
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
              let uu____386 = FStar_String.get s (Prims.parse_int "0") in
              uu____384 <> uu____386 in
            if uu____383 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s1])
let (infix_prim_ops
  :(Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
     FStar_Pervasives_Native.tuple3 Prims.list)=
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
let (prim_uni_ops
  :(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)=
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")]
let prim_types : 'Auu____630 . Prims.unit -> 'Auu____630 Prims.list=
  fun uu____633  -> []
let (prim_constructors
  :(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)=
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let (is_prims_ns
  :FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool)=
  fun ns  -> ns = ["Prims"]
let (as_bin_op
  :FStar_Extraction_ML_Syntax.mlpath ->
     (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                            FStar_Pervasives_Native.tuple2,
       Prims.string) FStar_Pervasives_Native.tuple3
       FStar_Pervasives_Native.option)=
  fun uu____685  ->
    match uu____685 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____730  ->
               match uu____730 with | (y,uu____742,uu____743) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let (is_bin_op :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  ->
    let uu____767 = as_bin_op p in uu____767 <> FStar_Pervasives_Native.None
let (as_uni_op
  :FStar_Extraction_ML_Syntax.mlpath ->
     (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)=
  fun uu____811  ->
    match uu____811 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____837  -> match uu____837 with | (y,uu____843) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let (is_uni_op :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  ->
    let uu____853 = as_uni_op p in uu____853 <> FStar_Pervasives_Native.None
let (is_standard_type :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  -> false
let (as_standard_constructor
  :FStar_Extraction_ML_Syntax.mlpath ->
     (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)=
  fun uu____883  ->
    match uu____883 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____909  -> match uu____909 with | (y,uu____915) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let (is_standard_constructor
  :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  ->
    let uu____925 = as_standard_constructor p in
    uu____925 <> FStar_Pervasives_Native.None
let (maybe_paren
  :((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
     FStar_Pervasives_Native.tuple2 ->
     (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
       FStar_Format.doc -> FStar_Format.doc)=
  fun uu____963  ->
    fun inner  ->
      fun doc1  ->
        match uu____963 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1014 = _inner in
              match uu____1014 with
              | (pi,fi) ->
                  let uu____1021 = _outer in
                  (match uu____1021 with
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
                           | (uu____1028,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1029,uu____1030) -> false))) in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
let (escape_byte_hex :FStar_BaseTypes.byte -> Prims.string)=
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let (escape_char_hex :FStar_BaseTypes.char -> Prims.string)=
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let (escape_or
  :(FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string)=
  fun fallback  ->
    fun uu___123_1050  ->
      match uu___123_1050 with
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
let (string_of_mlconstant
  :FStar_Extraction_ML_Syntax.mlconstant -> Prims.string)=
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let uu____1070 =
          let uu____1071 = escape_or escape_char_hex c in
          Prims.strcat uu____1071 "'" in
        Prims.strcat "'" uu____1070
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1095,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1107,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1133 =
          let uu____1134 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1134 "\"" in
        Prims.strcat "\"" uu____1133
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1136 =
          let uu____1137 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1137 "\"" in
        Prims.strcat "\"" uu____1136
    | uu____1138 ->
        failwith "TODO: extract integer constants properly into OCaml"
let rec (doc_of_mltype'
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)=
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s '_' 'u'
              else s in
            let uu____1160 =
              let uu____1161 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____1161 in
            FStar_Format.text uu____1160
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____1173 =
                let uu____1174 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1174 in
              FStar_Format.parens uu____1173 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1187 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1197 =
                    let uu____1198 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1198 in
                  FStar_Format.parens uu____1197 in
            let name1 = ptsym currentModule name in
            let uu____1200 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1200
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1202,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1214 =
              let uu____1215 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1215 in
            maybe_paren outer t_prio_fun uu____1214
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1216 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1216
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and (doc_of_mltype
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)=
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1221 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1221
let rec (doc_of_expr
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)=
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let uu____1275 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____1275
            then
              let uu____1276 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____1276
            else
              (let uu____1278 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1278)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____1294 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____1294
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1296 = string_of_mlconstant c in
            FStar_Format.text uu____1296
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____1298) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1300 = ptsym currentModule path in
            FStar_Format.text uu____1300
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1326 =
              match uu____1326 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1338 =
                    let uu____1341 =
                      let uu____1342 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1342 in
                    [uu____1341; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1338 in
            let uu____1345 =
              let uu____1346 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1346 in
            FStar_Format.cbrackets uu____1345
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1357 = is_standard_constructor ctor in
              if uu____1357
              then
                let uu____1358 =
                  let uu____1363 = as_standard_constructor ctor in
                  FStar_Option.get uu____1363 in
                FStar_Pervasives_Native.snd uu____1358
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1382 = is_standard_constructor ctor in
              if uu____1382
              then
                let uu____1383 =
                  let uu____1388 = as_standard_constructor ctor in
                  FStar_Option.get uu____1388 in
                FStar_Pervasives_Native.snd uu____1383
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1414,uu____1415) ->
                  let uu____1420 =
                    let uu____1423 =
                      let uu____1426 =
                        let uu____1427 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1427 in
                      [uu____1426] in
                    (FStar_Format.text name) :: uu____1423 in
                  FStar_Format.reduce1 uu____1420 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____1437 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1437) es in
            let docs2 =
              let uu____1443 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____1443 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1445,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1461 =
                  let uu____1464 =
                    let uu____1467 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1467] in
                  FStar_Format.hardline :: uu____1464 in
                FStar_Format.reduce uu____1461
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1477 =
              let uu____1478 =
                let uu____1481 =
                  let uu____1484 =
                    let uu____1487 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1487] in
                  doc1 :: uu____1484 in
                pre :: uu____1481 in
              FStar_Format.combine FStar_Format.hardline uu____1478 in
            FStar_Format.parens uu____1477
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1497::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1499;
                    FStar_Extraction_ML_Syntax.loc = uu____1500;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1502)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1504;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1505;_}::[])
                 when
                 let uu____1540 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1540 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1563;
                            FStar_Extraction_ML_Syntax.loc = uu____1564;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1566;
                       FStar_Extraction_ML_Syntax.loc = uu____1567;_} when
                       let uu____1588 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1589 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1588 = uu____1589 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1625;
                   FStar_Extraction_ML_Syntax.loc = uu____1626;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1639;
                   FStar_Extraction_ML_Syntax.loc = uu____1640;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1647 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1666 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1666)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1675 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1675
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1679 =
                   let uu____1682 =
                     let uu____1685 =
                       let uu____1688 =
                         let uu____1689 = ptsym currentModule f in
                         FStar_Format.text uu____1689 in
                       [uu____1688] in
                     (FStar_Format.text ".") :: uu____1685 in
                   e2 :: uu____1682 in
                 FStar_Format.reduce uu____1679) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1715 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1715
              then
                let uu____1716 =
                  let uu____1719 =
                    let uu____1722 =
                      let uu____1725 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1727 =
                              let uu____1730 =
                                let uu____1733 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1733] in
                              (FStar_Format.text " : ") :: uu____1730 in
                            FStar_Format.reduce1 uu____1727
                        | uu____1734 -> FStar_Format.text "" in
                      [uu____1725; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1722 in
                  (FStar_Format.text "(") :: uu____1719 in
                FStar_Format.reduce1 uu____1716
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1753  ->
                   match uu____1753 with
                   | ((x,uu____1763),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1775 =
                let uu____1778 =
                  let uu____1781 = FStar_Format.reduce1 ids1 in
                  [uu____1781; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1778 in
              FStar_Format.reduce1 uu____1775 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1792 =
                let uu____1795 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1796 =
                  let uu____1799 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1799; FStar_Format.text "end"] in
                uu____1795 :: uu____1796 in
              FStar_Format.combine FStar_Format.hardline uu____1792 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1815 =
                let uu____1818 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1819 =
                  let uu____1822 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1827 =
                    let uu____1830 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1831 =
                      let uu____1834 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1834; FStar_Format.text "end"] in
                    uu____1830 :: uu____1831 in
                  uu____1822 :: uu____1827 in
                uu____1818 :: uu____1819 in
              FStar_Format.combine FStar_Format.hardline uu____1815 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1872 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1872 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1877 =
              let uu____1880 =
                let uu____1883 =
                  let uu____1884 = ptctor currentModule exn in
                  FStar_Format.text uu____1884 in
                [uu____1883] in
              (FStar_Format.text "raise") :: uu____1880 in
            FStar_Format.reduce1 uu____1877
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1898 =
              let uu____1901 =
                let uu____1904 =
                  let uu____1905 = ptctor currentModule exn in
                  FStar_Format.text uu____1905 in
                let uu____1906 =
                  let uu____1909 =
                    let uu____1910 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1910 in
                  [uu____1909] in
                uu____1904 :: uu____1906 in
              (FStar_Format.text "raise") :: uu____1901 in
            FStar_Format.reduce1 uu____1898
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1933 =
              let uu____1936 =
                let uu____1939 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1944 =
                  let uu____1947 =
                    let uu____1950 =
                      let uu____1951 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1951 in
                    [uu____1950] in
                  (FStar_Format.text "with") :: uu____1947 in
                uu____1939 :: uu____1944 in
              (FStar_Format.text "try") :: uu____1936 in
            FStar_Format.combine FStar_Format.hardline uu____1933
and (doc_of_binop
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath ->
       FStar_Extraction_ML_Syntax.mlexpr ->
         FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)=
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____1958 =
            let uu____1969 = as_bin_op p in FStar_Option.get uu____1969 in
          match uu____1958 with
          | (uu____1992,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1 in
              let e21 = doc_of_expr currentModule (prio, Right) e2 in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21] in
              FStar_Format.parens doc1
and (doc_of_uniop
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath ->
       FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)=
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____2017 =
          let uu____2022 = as_uni_op p in FStar_Option.get uu____2022 in
        match uu____2017 with
        | (uu____2033,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11] in
            FStar_Format.parens doc1
and (doc_of_pattern
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc)=
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____2044 = string_of_mlconstant c in
          FStar_Format.text uu____2044
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2071 =
            match uu____2071 with
            | (name,p) ->
                let uu____2078 =
                  let uu____2081 =
                    let uu____2082 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2082 in
                  let uu____2085 =
                    let uu____2088 =
                      let uu____2091 = doc_of_pattern currentModule p in
                      [uu____2091] in
                    (FStar_Format.text "=") :: uu____2088 in
                  uu____2081 :: uu____2085 in
                FStar_Format.reduce1 uu____2078 in
          let uu____2092 =
            let uu____2093 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2093 in
          FStar_Format.cbrackets uu____2092
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2104 = is_standard_constructor ctor in
            if uu____2104
            then
              let uu____2105 =
                let uu____2110 = as_standard_constructor ctor in
                FStar_Option.get uu____2110 in
              FStar_Pervasives_Native.snd uu____2105
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2129 = is_standard_constructor ctor in
            if uu____2129
            then
              let uu____2130 =
                let uu____2135 = as_standard_constructor ctor in
                FStar_Option.get uu____2135 in
              FStar_Pervasives_Native.snd uu____2130
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2154 =
                  let uu____2157 =
                    let uu____2158 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2158 in
                  let uu____2159 =
                    let uu____2162 =
                      let uu____2165 = doc_of_pattern currentModule xs in
                      [uu____2165] in
                    (FStar_Format.text "::") :: uu____2162 in
                  uu____2157 :: uu____2159 in
                FStar_Format.reduce uu____2154
            | (uu____2166,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2167)::[]) ->
                let uu____2172 =
                  let uu____2175 =
                    let uu____2178 =
                      let uu____2179 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2179 in
                    [uu____2178] in
                  (FStar_Format.text name) :: uu____2175 in
                FStar_Format.reduce1 uu____2172
            | uu____2180 ->
                let uu____2187 =
                  let uu____2190 =
                    let uu____2193 =
                      let uu____2194 =
                        let uu____2195 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2195 in
                      FStar_Format.parens uu____2194 in
                    [uu____2193] in
                  (FStar_Format.text name) :: uu____2190 in
                FStar_Format.reduce1 uu____2187 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2208 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2208
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and (doc_of_branch
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)=
  fun currentModule  ->
    fun uu____2219  ->
      match uu____2219 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2228 =
                  let uu____2231 =
                    let uu____2234 = doc_of_pattern currentModule p in
                    [uu____2234] in
                  (FStar_Format.text "|") :: uu____2231 in
                FStar_Format.reduce1 uu____2228
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2241 =
                  let uu____2244 =
                    let uu____2247 = doc_of_pattern currentModule p in
                    [uu____2247; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2244 in
                FStar_Format.reduce1 uu____2241 in
          let uu____2248 =
            let uu____2251 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2252 =
              let uu____2255 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2255; FStar_Format.text "end"] in
            uu____2251 :: uu____2252 in
          FStar_Format.combine FStar_Format.hardline uu____2248
and (doc_of_lets
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                          Prims.list)
       FStar_Pervasives_Native.tuple3 -> FStar_Format.doc)=
  fun currentModule  ->
    fun uu____2261  ->
      match uu____2261 with
      | (rec_,top_level,lets) ->
          let for1 uu____2280 =
            match uu____2280 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2283;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2298 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2298
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2299::uu____2300,uu____2301) ->
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
                                let uu____2353 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu____2353
                                  FStar_Format.reduce1 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "") in
                let uu____2367 =
                  let uu____2370 =
                    let uu____2371 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____2371 in
                  let uu____2372 =
                    let uu____2375 = FStar_Format.reduce1 ids in
                    [uu____2375; ty_annot; FStar_Format.text "="; e1] in
                  uu____2370 :: uu____2372 in
                FStar_Format.reduce1 uu____2367 in
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
and (doc_of_loc :FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc)=
  fun uu____2389  ->
    match uu____2389 with
    | (lineno,file) ->
        let uu____2392 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____2392
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])
let (doc_of_mltydecl
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc)=
  fun currentModule  ->
    fun decls  ->
      let for1 uu____2424 =
        match uu____2424 with
        | (uu____2443,x,mangle_opt,tparams,uu____2447,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____2465 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____2465
              | uu____2466 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____2475 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____2475) tparams in
                  let uu____2476 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2476 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2500 =
                    match uu____2500 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2513 =
                    let uu____2514 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2514 in
                  FStar_Format.cbrackets uu____2513
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2547 =
                    match uu____2547 with
                    | (name,tys) ->
                        let uu____2572 = FStar_List.split tys in
                        (match uu____2572 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2591 ->
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
              let uu____2621 =
                let uu____2624 =
                  let uu____2627 =
                    let uu____2628 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2628 in
                  [uu____2627] in
                tparams1 :: uu____2624 in
              FStar_Format.reduce1 uu____2621 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2633 =
                   let uu____2636 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2636; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2633) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2659 =
            let uu____2662 =
              let uu____2665 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2665] in
            (FStar_Format.text "type") :: uu____2662 in
          FStar_Format.reduce1 uu____2659
        else FStar_Format.text "" in
      doc2
let rec (doc_of_sig1
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc)=
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____2683 =
            let uu____2686 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____2687 =
              let uu____2690 = doc_of_sig currentModule subsig in
              let uu____2691 =
                let uu____2694 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____2694] in
              uu____2690 :: uu____2691 in
            uu____2686 :: uu____2687 in
          FStar_Format.combine FStar_Format.hardline uu____2683
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____2712 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____2712 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2714,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and (doc_of_sig
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc)=
  fun currentModule  ->
    fun s  ->
      let docs1 = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs2 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs1 in
      FStar_Format.reduce docs2
let (doc_of_mod1
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc)=
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
            let uu____2784 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____2784 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____2787,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____2796 =
            let uu____2799 =
              let uu____2802 =
                let uu____2805 =
                  let uu____2808 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____2808] in
                (FStar_Format.text "=") :: uu____2805 in
              (FStar_Format.text "_") :: uu____2802 in
            (FStar_Format.text "let") :: uu____2799 in
          FStar_Format.reduce1 uu____2796
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let (doc_of_mod
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc)=
  fun currentModule  ->
    fun m  ->
      let docs1 =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2834 ->
                  FStar_Format.empty
              | uu____2835 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec (doc_of_mllib_r
  :FStar_Extraction_ML_Syntax.mllib ->
     (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2
       Prims.list)=
  fun uu____2845  ->
    match uu____2845 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2911 =
          match uu____2911 with
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
                  (fun uu____2984  ->
                     match uu____2984 with
                     | (s,uu____2990) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____3017 =
                let uu____3020 =
                  let uu____3023 =
                    let uu____3026 = FStar_Format.reduce sub3 in
                    [uu____3026;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3023 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3020 in
              FStar_Format.reduce uu____3017
        and for1_mod istop uu____3029 =
          match uu____3029 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3097 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3108 =
                  let uu____3111 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____3111
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
                FStar_Format.reduce1 uu____3108 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3130  ->
                     match uu____3130 with
                     | (uu____3135,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3166 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____3166
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3170 =
                let uu____3173 =
                  let uu____3176 =
                    let uu____3179 =
                      let uu____3182 =
                        let uu____3185 =
                          let uu____3188 = FStar_Format.reduce sub3 in
                          [uu____3188;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3185 in
                      FStar_Format.hardline :: uu____3182 in
                    FStar_List.append maybe_open_pervasives uu____3179 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3176 in
                FStar_List.append prefix1 uu____3173 in
              FStar_All.pipe_left FStar_Format.reduce uu____3170 in
        let docs1 =
          FStar_List.map
            (fun uu____3227  ->
               match uu____3227 with
               | (x,s,m) ->
                   let uu____3277 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3278 = for1_mod true (x, s, m) in
                   (uu____3277, uu____3278)) mllib in
        docs1
let (doc_of_mllib
  :FStar_Extraction_ML_Syntax.mllib ->
     (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2
       Prims.list)=
  fun mllib  -> doc_of_mllib_r mllib
let (string_of_mlexpr
  :FStar_Extraction_ML_Syntax.mlpath ->
     FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)=
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3310 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3310 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let (string_of_mlty
  :FStar_Extraction_ML_Syntax.mlpath ->
     FStar_Extraction_ML_Syntax.mlty -> Prims.string)=
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3324 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3324 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1