open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let uu___is_ILeft : assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____6 -> false 
let uu___is_IRight : assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____12 -> false
  
let uu___is_Left : assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____18 -> false 
let uu___is_Right : assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____24 -> false 
let uu___is_NonAssoc : assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____30 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc [@@deriving show]
let uu___is_Prefix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____41 -> false
  
let uu___is_Postfix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____47 -> false
  
let uu___is_Infix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____54 -> false
  
let __proj__Infix__item___0 : fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2[@@deriving show]
let t_prio_fun : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (10)), (Infix Right)) 
let t_prio_tpl : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (20)), (Infix NonAssoc)) 
let t_prio_name : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (30)), Postfix) 
let e_bin_prio_lambda : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (5)), Prefix) 
let e_bin_prio_if : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (15)), Prefix) 
let e_bin_prio_letin : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (19)), Prefix) 
let e_bin_prio_or : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (20)), (Infix Left)) 
let e_bin_prio_and : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (25)), (Infix Left)) 
let e_bin_prio_eq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (27)), (Infix NonAssoc)) 
let e_bin_prio_order : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (29)), (Infix NonAssoc)) 
let e_bin_prio_op1 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (30)), (Infix Left)) 
let e_bin_prio_op2 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (40)), (Infix Left)) 
let e_bin_prio_op3 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (50)), (Infix Left)) 
let e_bin_prio_op4 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (60)), (Infix Left)) 
let e_bin_prio_comb : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (70)), (Infix Left)) 
let e_bin_prio_seq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (100)), (Infix Left)) 
let e_app_prio : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.lift_native_int (10000)), (Infix Left)) 
let min_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((~- (Prims.lift_native_int (1))), (Infix NonAssoc)) 
let max_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns :
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool
  =
  fun x  ->
    match x with
    | ([],uu____173) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____196,uu____197) -> false
  
let path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
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
                  let uu____259 = FStar_Util.first_N cg_len ns  in
                  match uu____259 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____292 =
                           let uu____295 =
                             let uu____298 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____298]  in
                           FStar_List.append pfx uu____295  in
                         FStar_Pervasives_Native.Some uu____292
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None)
            in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
  
let mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____326 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____326 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____331 ->
          let uu____332 = x  in
          (match uu____332 with
           | (ns,x1) ->
               let uu____339 = path_of_ns currentModule ns  in
               (uu____339, x1))
  
let ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____349 =
      let uu____350 =
        let uu____352 = FStar_String.get s (Prims.lift_native_int (0))  in
        FStar_Char.lowercase uu____352  in
      let uu____354 = FStar_String.get s (Prims.lift_native_int (0))  in
      uu____350 <> uu____354  in
    if uu____349 then Prims.strcat "l__" s else s
  
let ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____373 = mlpath_of_mlpath currentModule mlp  in
         match uu____373 with
         | (p,s) ->
             let uu____380 =
               let uu____383 =
                 let uu____386 = ptsym_of_symbol s  in [uu____386]  in
               FStar_List.append p uu____383  in
             FStar_String.concat "." uu____380)
  
let ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____397 = mlpath_of_mlpath currentModule mlp  in
      match uu____397 with
      | (p,s) ->
          let s1 =
            let uu____405 =
              let uu____406 =
                let uu____408 =
                  FStar_String.get s (Prims.lift_native_int (0))  in
                FStar_Char.uppercase uu____408  in
              let uu____410 = FStar_String.get s (Prims.lift_native_int (0))
                 in
              uu____406 <> uu____410  in
            if uu____405 then Prims.strcat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
  
let infix_prim_ops :
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
let prim_uni_ops :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____642  ->
    let op_minus =
      let uu____644 =
        let uu____645 = FStar_Options.codegen ()  in
        uu____645 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____644 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____669 . unit -> 'Auu____669 Prims.list =
  fun uu____672  -> [] 
let prim_constructors :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool =
  fun ns  -> ns = ["Prims"] 
let as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option
  =
  fun uu____726  ->
    match uu____726 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____771  ->
               match uu____771 with | (y,uu____783,uu____784) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____809 = as_bin_op p  in uu____809 <> FStar_Pervasives_Native.None
  
let as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____854  ->
    match uu____854 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____873 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____887  -> match uu____887 with | (y,uu____893) -> x = y)
            uu____873
        else FStar_Pervasives_Native.None
  
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____904 = as_uni_op p  in uu____904 <> FStar_Pervasives_Native.None
  
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false 
let as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____936  ->
    match uu____936 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____962  -> match uu____962 with | (y,uu____968) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____979 = as_standard_constructor p  in
    uu____979 <> FStar_Pervasives_Native.None
  
let maybe_paren :
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____1020  ->
    fun inner  ->
      fun doc1  ->
        match uu____1020 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1077 = _inner  in
              match uu____1077 with
              | (pi,fi) ->
                  let uu____1084 = _outer  in
                  (match uu____1084 with
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
                           | (uu____1091,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1092,uu____1093) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let escape_byte_hex : FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let escape_char_hex : FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let escape_or :
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___63_1119  ->
      match uu___63_1119 with
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
  
let string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1171 = FStar_Util.string_of_int nc  in
        Prims.strcat uu____1171
          (if
             ((nc >= (Prims.lift_native_int (32))) &&
                (nc <= (Prims.lift_native_int (127))))
               && (nc <> (Prims.lift_native_int (34)))
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
        (s,FStar_Pervasives_Native.Some (uu____1218,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1230,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        let threshold = (Prims.lift_native_int (1073741823))  in
        let is = FStar_Util.int_of_string s  in
        if ((- threshold) <= is) && (is <= threshold)
        then Prims.strcat "(Prims.lift_native_int (" (Prims.strcat s "))")
        else Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1259 =
          let uu____1260 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat uu____1260 "\""  in
        Prims.strcat "\"" uu____1259
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1262 =
          let uu____1263 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat uu____1263 "\""  in
        Prims.strcat "\"" uu____1262
    | uu____1264 ->
        failwith "TODO: extract integer constants properly into OCaml"
  
let rec doc_of_mltype' :
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
              else s  in
            FStar_Format.text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc2 =
              let uu____1313 =
                let uu____1314 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____1314  in
              FStar_Format.parens uu____1313  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1327 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____1337 =
                    let uu____1338 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____1338  in
                  FStar_Format.parens uu____1337
               in
            let name1 = ptsym currentModule name  in
            let uu____1340 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____1340
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1342,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____1354 =
              let uu____1355 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____1355  in
            maybe_paren outer t_prio_fun uu____1354
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1356 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1356
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> FStar_Format.text "unit"

and doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1361 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____1361

let rec doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____1449 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1449
            then
              let uu____1450 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____1450
            else
              (let uu____1452 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____1452)
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
            let uu____1468 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____1468
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1470 = string_of_mlconstant c  in
            FStar_Format.text uu____1470
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1473 = ptsym currentModule path  in
            FStar_Format.text uu____1473
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1501 =
              match uu____1501 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1513 =
                    let uu____1516 =
                      let uu____1517 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____1517  in
                    [uu____1516; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____1513
               in
            let uu____1520 =
              let uu____1521 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____1521  in
            FStar_Format.cbrackets uu____1520
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1532 = is_standard_constructor ctor  in
              if uu____1532
              then
                let uu____1533 =
                  let uu____1538 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1538  in
                FStar_Pervasives_Native.snd uu____1533
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1557 = is_standard_constructor ctor  in
              if uu____1557
              then
                let uu____1558 =
                  let uu____1563 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1563  in
                FStar_Pervasives_Native.snd uu____1558
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
              | (uu____1589,uu____1590) ->
                  let uu____1595 =
                    let uu____1598 =
                      let uu____1601 =
                        let uu____1602 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____1602  in
                      [uu____1601]  in
                    (FStar_Format.text name) :: uu____1598  in
                  FStar_Format.reduce1 uu____1595
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____1612 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____1612) es
               in
            let docs1 =
              let uu____1618 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____1618  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1633 =
                  let uu____1636 =
                    let uu____1639 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____1639]  in
                  FStar_Format.hardline :: uu____1636  in
                FStar_Format.reduce uu____1633
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____1649 =
              let uu____1650 =
                let uu____1653 =
                  let uu____1656 =
                    let uu____1659 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____1659]  in
                  doc1 :: uu____1656  in
                pre :: uu____1653  in
              FStar_Format.combine FStar_Format.hardline uu____1650  in
            FStar_Format.parens uu____1649
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1669::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1671;
                    FStar_Extraction_ML_Syntax.loc = uu____1672;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1674)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1676;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1677;_}::[])
                 when
                 let uu____1712 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____1712 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1735;
                            FStar_Extraction_ML_Syntax.loc = uu____1736;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1738;
                       FStar_Extraction_ML_Syntax.loc = uu____1739;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1795;
                   FStar_Extraction_ML_Syntax.loc = uu____1796;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1809;
                   FStar_Extraction_ML_Syntax.loc = uu____1810;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1817 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____1836 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____1836)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____1845 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1845
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1849 =
                   let uu____1852 =
                     let uu____1855 =
                       let uu____1858 =
                         let uu____1859 = ptsym currentModule f  in
                         FStar_Format.text uu____1859  in
                       [uu____1858]  in
                     (FStar_Format.text ".") :: uu____1855  in
                   e2 :: uu____1852  in
                 FStar_Format.reduce uu____1849)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1889 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1889
              then
                let uu____1890 =
                  let uu____1893 =
                    let uu____1896 =
                      let uu____1899 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1901 =
                              let uu____1904 =
                                let uu____1907 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____1907]  in
                              (FStar_Format.text " : ") :: uu____1904  in
                            FStar_Format.reduce1 uu____1901
                        | uu____1908 -> FStar_Format.text ""  in
                      [uu____1899; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____1896  in
                  (FStar_Format.text "(") :: uu____1893  in
                FStar_Format.reduce1 uu____1890
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____1922  ->
                   match uu____1922 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____1935 =
                let uu____1938 =
                  let uu____1941 = FStar_Format.reduce1 ids1  in
                  [uu____1941; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____1938  in
              FStar_Format.reduce1 uu____1935  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1952 =
                let uu____1955 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1956 =
                  let uu____1959 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____1959; FStar_Format.text "end"]  in
                uu____1955 :: uu____1956  in
              FStar_Format.combine FStar_Format.hardline uu____1952  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1975 =
                let uu____1978 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1979 =
                  let uu____1982 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1987 =
                    let uu____1990 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____1991 =
                      let uu____1994 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____1994; FStar_Format.text "end"]  in
                    uu____1990 :: uu____1991  in
                  uu____1982 :: uu____1987  in
                uu____1978 :: uu____1979  in
              FStar_Format.combine FStar_Format.hardline uu____1975  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2032 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____2032 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2037 =
              let uu____2040 =
                let uu____2043 =
                  let uu____2044 = ptctor currentModule exn  in
                  FStar_Format.text uu____2044  in
                [uu____2043]  in
              (FStar_Format.text "raise") :: uu____2040  in
            FStar_Format.reduce1 uu____2037
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2058 =
              let uu____2061 =
                let uu____2064 =
                  let uu____2065 = ptctor currentModule exn  in
                  FStar_Format.text uu____2065  in
                let uu____2066 =
                  let uu____2069 =
                    let uu____2070 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____2070  in
                  [uu____2069]  in
                uu____2064 :: uu____2066  in
              (FStar_Format.text "raise") :: uu____2061  in
            FStar_Format.reduce1 uu____2058
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2093 =
              let uu____2096 =
                let uu____2099 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2104 =
                  let uu____2107 =
                    let uu____2110 =
                      let uu____2111 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____2111
                       in
                    [uu____2110]  in
                  (FStar_Format.text "with") :: uu____2107  in
                uu____2099 :: uu____2104  in
              (FStar_Format.text "try") :: uu____2096  in
            FStar_Format.combine FStar_Format.hardline uu____2093
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1

and doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____2124 =
            let uu____2135 = as_bin_op p  in FStar_Option.get uu____2135  in
          match uu____2124 with
          | (uu____2158,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21]  in
              FStar_Format.parens doc1

and doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____2183 =
          let uu____2188 = as_uni_op p  in FStar_Option.get uu____2188  in
        match uu____2183 with
        | (uu____2199,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11]
               in
            FStar_Format.parens doc1

and doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____2210 = string_of_mlconstant c  in
          FStar_Format.text uu____2210
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2239 =
            match uu____2239 with
            | (name,p) ->
                let uu____2246 =
                  let uu____2249 =
                    let uu____2250 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2250  in
                  let uu____2253 =
                    let uu____2256 =
                      let uu____2259 = doc_of_pattern currentModule p  in
                      [uu____2259]  in
                    (FStar_Format.text "=") :: uu____2256  in
                  uu____2249 :: uu____2253  in
                FStar_Format.reduce1 uu____2246
             in
          let uu____2260 =
            let uu____2261 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____2261  in
          FStar_Format.cbrackets uu____2260
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2272 = is_standard_constructor ctor  in
            if uu____2272
            then
              let uu____2273 =
                let uu____2278 = as_standard_constructor ctor  in
                FStar_Option.get uu____2278  in
              FStar_Pervasives_Native.snd uu____2273
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2297 = is_standard_constructor ctor  in
            if uu____2297
            then
              let uu____2298 =
                let uu____2303 = as_standard_constructor ctor  in
                FStar_Option.get uu____2303  in
              FStar_Pervasives_Native.snd uu____2298
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2322 =
                  let uu____2325 =
                    let uu____2326 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____2326  in
                  let uu____2327 =
                    let uu____2330 =
                      let uu____2333 = doc_of_pattern currentModule xs  in
                      [uu____2333]  in
                    (FStar_Format.text "::") :: uu____2330  in
                  uu____2325 :: uu____2327  in
                FStar_Format.reduce uu____2322
            | (uu____2334,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2335)::[]) ->
                let uu____2340 =
                  let uu____2343 =
                    let uu____2346 =
                      let uu____2347 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____2347  in
                    [uu____2346]  in
                  (FStar_Format.text name) :: uu____2343  in
                FStar_Format.reduce1 uu____2340
            | uu____2348 ->
                let uu____2355 =
                  let uu____2358 =
                    let uu____2361 =
                      let uu____2362 =
                        let uu____2363 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2363
                         in
                      FStar_Format.parens uu____2362  in
                    [uu____2361]  in
                  (FStar_Format.text name) :: uu____2358  in
                FStar_Format.reduce1 uu____2355
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____2376 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____2376
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2387  ->
      match uu____2387 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2396 =
                  let uu____2399 =
                    let uu____2402 = doc_of_pattern currentModule p  in
                    [uu____2402]  in
                  (FStar_Format.text "|") :: uu____2399  in
                FStar_Format.reduce1 uu____2396
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____2409 =
                  let uu____2412 =
                    let uu____2415 = doc_of_pattern currentModule p  in
                    [uu____2415; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____2412  in
                FStar_Format.reduce1 uu____2409
             in
          let uu____2416 =
            let uu____2419 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____2420 =
              let uu____2423 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____2423; FStar_Format.text "end"]  in
            uu____2419 :: uu____2420  in
          FStar_Format.combine FStar_Format.hardline uu____2416

and doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2429  ->
      match uu____2429 with
      | (rec_,top_level,lets) ->
          let for1 uu____2450 =
            match uu____2450 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2453;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____2455;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2469 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____2469
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2470::uu____2471,uu____2472) ->
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
                                let uu____2524 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____2524
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____2538 =
                  let uu____2541 =
                    let uu____2544 = FStar_Format.reduce1 ids  in
                    [uu____2544; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____2541  in
                FStar_Format.reduce1 uu____2538
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
                     [if i = (Prims.lift_native_int (0))
                      then letdoc
                      else FStar_Format.text "and";
                     doc1]) lets1
             in
          FStar_Format.combine FStar_Format.hardline lets2

and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____2558  ->
    match uu____2558 with
    | (lineno,file) ->
        let uu____2561 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____2561
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])

let doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____2597 =
        match uu____2597 with
        | (uu____2616,x,mangle_opt,tparams,uu____2620,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2638 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____2646 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____2646
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2674 =
                    match uu____2674 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____2687 =
                    let uu____2688 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2688
                     in
                  FStar_Format.cbrackets uu____2687
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2723 =
                    match uu____2723 with
                    | (name,tys) ->
                        let uu____2748 = FStar_List.split tys  in
                        (match uu____2748 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2767 ->
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
              let uu____2797 =
                let uu____2800 =
                  let uu____2803 =
                    let uu____2804 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____2804  in
                  [uu____2803]  in
                tparams1 :: uu____2800  in
              FStar_Format.reduce1 uu____2797  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____2809 =
                   let uu____2812 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____2812; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____2809)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.lift_native_int (0))
        then
          let uu____2835 =
            let uu____2838 =
              let uu____2841 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____2841]  in
            (FStar_Format.text "type") :: uu____2838  in
          FStar_Format.reduce1 uu____2835
        else FStar_Format.text ""  in
      doc2
  
let rec doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____2867 =
            let uu____2870 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____2871 =
              let uu____2874 = doc_of_sig currentModule subsig  in
              let uu____2875 =
                let uu____2878 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____2878]  in
              uu____2874 :: uu____2875  in
            uu____2870 :: uu____2871  in
          FStar_Format.combine FStar_Format.hardline uu____2867
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____2896 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____2896  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2898,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
             in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls

and doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
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

let doc_of_mod1 :
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
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args  in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1
             in
          let args3 =
            let uu____2970 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____2970  in
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
          let uu____2981 =
            let uu____2984 =
              let uu____2987 =
                let uu____2990 =
                  let uu____2993 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____2993]  in
                (FStar_Format.text "=") :: uu____2990  in
              (FStar_Format.text "_") :: uu____2987  in
            (FStar_Format.text "let") :: uu____2984  in
          FStar_Format.reduce1 uu____2981
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
  
let doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x  in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____3021 ->
                  FStar_Format.empty
              | uu____3022 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3033  ->
    match uu____3033 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____3105 =
          match uu____3105 with
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
                  (fun uu____3178  ->
                     match uu____3178 with
                     | (s,uu____3184) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____3211 =
                let uu____3214 =
                  let uu____3217 =
                    let uu____3220 = FStar_Format.reduce sub3  in
                    [uu____3220;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3217
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3214
                 in
              FStar_Format.reduce uu____3211
        
        and for1_mod istop uu____3223 =
          match uu____3223 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3291 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)]
                 in
              let head1 =
                let uu____3302 =
                  let uu____3305 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____3305
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
                FStar_Format.reduce1 uu____3302  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____3324  ->
                     match uu____3324 with
                     | (uu____3329,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____3360 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____3360
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____3364 =
                let uu____3367 =
                  let uu____3370 =
                    let uu____3373 =
                      let uu____3376 =
                        let uu____3379 =
                          let uu____3382 = FStar_Format.reduce sub3  in
                          [uu____3382;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3379
                         in
                      FStar_Format.hardline :: uu____3376  in
                    FStar_List.append maybe_open_pervasives uu____3373  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3370
                   in
                FStar_List.append prefix1 uu____3367  in
              FStar_All.pipe_left FStar_Format.reduce uu____3364
         in
        let docs =
          FStar_List.map
            (fun uu____3421  ->
               match uu____3421 with
               | (x,s,m) ->
                   let uu____3471 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____3472 = for1_mod true (x, s, m)  in
                   (uu____3471, uu____3472)) mllib
           in
        docs
  
let doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib 
let string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3507 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____3507 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.lift_native_int (0)) doc1
  
let string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3523 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____3523 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.lift_native_int (0)) doc1
  