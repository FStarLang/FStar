open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | ILeft  -> true | uu____4 -> false 
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | IRight  -> true | uu____8 -> false 
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____12 -> false 
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  -> match projectee with | Right  -> true | uu____16 -> false 
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____20 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc [@@deriving show]
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____28 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____32 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____37 -> false
  
let (__proj__Infix__item___0 : fixity -> assoc) =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2[@@deriving show]
let (t_prio_fun : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "10"), (Infix Right)) 
let (t_prio_tpl : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let (t_prio_name : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "30"), Postfix) 
let (e_bin_prio_lambda : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "5"), Prefix) 
let (e_bin_prio_if : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "15"), Prefix) 
let (e_bin_prio_letin : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "19"), Prefix) 
let (e_bin_prio_or : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "20"), (Infix Left)) 
let (e_bin_prio_and : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "25"), (Infix Left)) 
let (e_bin_prio_eq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let (e_bin_prio_order : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let (e_bin_prio_op1 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "30"), (Infix Left)) 
let (e_bin_prio_op2 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "40"), (Infix Left)) 
let (e_bin_prio_op3 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "50"), (Infix Left)) 
let (e_bin_prio_op4 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "60"), (Infix Left)) 
let (e_bin_prio_comb : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "70"), (Infix Left)) 
let (e_bin_prio_seq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "100"), (Infix Left)) 
let (e_app_prio : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((Prims.parse_int "10000"), (Infix Left)) 
let (min_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let (max_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2) =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns :
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool
  =
  fun x  ->
    match x with
    | ([],uu____153) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____176,uu____177) -> false
  
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
                  let uu____235 = FStar_Util.first_N cg_len ns  in
                  match uu____235 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____268 =
                           let uu____271 =
                             let uu____274 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____274]  in
                           FStar_List.append pfx uu____271  in
                         FStar_Pervasives_Native.Some uu____268
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
      let uu____298 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____298 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____303 ->
          let uu____304 = x  in
          (match uu____304 with
           | (ns,x1) ->
               let uu____311 = path_of_ns currentModule ns  in
               (uu____311, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____319 =
      let uu____320 =
        let uu____322 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____322  in
      let uu____324 = FStar_String.get s (Prims.parse_int "0")  in
      uu____320 <> uu____324  in
    if uu____319 then Prims.strcat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____339 = mlpath_of_mlpath currentModule mlp  in
         match uu____339 with
         | (p,s) ->
             let uu____346 =
               let uu____349 =
                 let uu____352 = ptsym_of_symbol s  in [uu____352]  in
               FStar_List.append p uu____349  in
             FStar_String.concat "." uu____346)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____359 = mlpath_of_mlpath currentModule mlp  in
      match uu____359 with
      | (p,s) ->
          let s1 =
            let uu____367 =
              let uu____368 =
                let uu____370 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____370  in
              let uu____372 = FStar_String.get s (Prims.parse_int "0")  in
              uu____368 <> uu____372  in
            if uu____367 then Prims.strcat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
  
let (infix_prim_ops :
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list)
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
let (prim_uni_ops :
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____602  ->
    let op_minus =
      let uu____604 =
        let uu____605 = FStar_Options.codegen ()  in
        uu____605 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____604 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____628 . Prims.unit -> 'Auu____628 Prims.list =
  fun uu____631  -> [] 
let (prim_constructors :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let (is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool) =
  fun ns  -> ns = ["Prims"] 
let (as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun uu____681  ->
    match uu____681 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____726  ->
               match uu____726 with | (y,uu____738,uu____739) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____762 = as_bin_op p  in uu____762 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun uu____805  ->
    match uu____805 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____824 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____838  -> match uu____838 with | (y,uu____844) -> x = y)
            uu____824
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____853 = as_uni_op p  in uu____853 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun uu____881  ->
    match uu____881 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____907  -> match uu____907 with | (y,uu____913) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____922 = as_standard_constructor p  in
    uu____922 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____957  ->
    fun inner  ->
      fun doc1  ->
        match uu____957 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1008 = _inner  in
              match uu____1008 with
              | (pi,fi) ->
                  let uu____1015 = _outer  in
                  (match uu____1015 with
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
                           | (uu____1022,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1023,uu____1024) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string) =
  fun fallback  ->
    fun uu___63_1042  ->
      match uu___63_1042 with
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
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1092 = FStar_Util.string_of_int nc  in
        Prims.strcat uu____1092
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
          let uu____1178 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat uu____1178 "\""  in
        Prims.strcat "\"" uu____1177
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1180 =
          let uu____1181 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat uu____1181 "\""  in
        Prims.strcat "\"" uu____1180
    | uu____1182 ->
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
              let uu____1217 =
                let uu____1218 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____1218  in
              FStar_Format.parens uu____1217  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1231 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____1241 =
                    let uu____1242 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____1242  in
                  FStar_Format.parens uu____1241
               in
            let name1 = ptsym currentModule name  in
            let uu____1244 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____1244
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1246,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____1258 =
              let uu____1259 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____1259  in
            maybe_paren outer t_prio_fun uu____1258
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1260 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1260
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1265 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____1265

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
            let uu____1319 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1319
            then
              let uu____1320 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____1320
            else
              (let uu____1322 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____1322)
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
            let uu____1338 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____1338
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1340 = string_of_mlconstant c  in
            FStar_Format.text uu____1340
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1343 = ptsym currentModule path  in
            FStar_Format.text uu____1343
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1369 =
              match uu____1369 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1381 =
                    let uu____1384 =
                      let uu____1385 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____1385  in
                    [uu____1384; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____1381
               in
            let uu____1388 =
              let uu____1389 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____1389  in
            FStar_Format.cbrackets uu____1388
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1400 = is_standard_constructor ctor  in
              if uu____1400
              then
                let uu____1401 =
                  let uu____1406 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1406  in
                FStar_Pervasives_Native.snd uu____1401
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1425 = is_standard_constructor ctor  in
              if uu____1425
              then
                let uu____1426 =
                  let uu____1431 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1431  in
                FStar_Pervasives_Native.snd uu____1426
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
              | (uu____1457,uu____1458) ->
                  let uu____1463 =
                    let uu____1466 =
                      let uu____1469 =
                        let uu____1470 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____1470  in
                      [uu____1469]  in
                    (FStar_Format.text name) :: uu____1466  in
                  FStar_Format.reduce1 uu____1463
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____1480 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____1480) es
               in
            let docs1 =
              let uu____1486 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____1486  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1501 =
                  let uu____1504 =
                    let uu____1507 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____1507]  in
                  FStar_Format.hardline :: uu____1504  in
                FStar_Format.reduce uu____1501
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____1517 =
              let uu____1518 =
                let uu____1521 =
                  let uu____1524 =
                    let uu____1527 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____1527]  in
                  doc1 :: uu____1524  in
                pre :: uu____1521  in
              FStar_Format.combine FStar_Format.hardline uu____1518  in
            FStar_Format.parens uu____1517
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1537::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1539;
                    FStar_Extraction_ML_Syntax.loc = uu____1540;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1542)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1544;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1545;_}::[])
                 when
                 let uu____1580 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____1580 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1603;
                            FStar_Extraction_ML_Syntax.loc = uu____1604;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1606;
                       FStar_Extraction_ML_Syntax.loc = uu____1607;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1663;
                   FStar_Extraction_ML_Syntax.loc = uu____1664;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1677;
                   FStar_Extraction_ML_Syntax.loc = uu____1678;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1685 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____1704 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____1704)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____1713 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1713
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1717 =
                   let uu____1720 =
                     let uu____1723 =
                       let uu____1726 =
                         let uu____1727 = ptsym currentModule f  in
                         FStar_Format.text uu____1727  in
                       [uu____1726]  in
                     (FStar_Format.text ".") :: uu____1723  in
                   e2 :: uu____1720  in
                 FStar_Format.reduce uu____1717)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1753 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1753
              then
                let uu____1754 =
                  let uu____1757 =
                    let uu____1760 =
                      let uu____1763 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1765 =
                              let uu____1768 =
                                let uu____1771 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____1771]  in
                              (FStar_Format.text " : ") :: uu____1768  in
                            FStar_Format.reduce1 uu____1765
                        | uu____1772 -> FStar_Format.text ""  in
                      [uu____1763; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____1760  in
                  (FStar_Format.text "(") :: uu____1757  in
                FStar_Format.reduce1 uu____1754
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____1786  ->
                   match uu____1786 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____1799 =
                let uu____1802 =
                  let uu____1805 = FStar_Format.reduce1 ids1  in
                  [uu____1805; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____1802  in
              FStar_Format.reduce1 uu____1799  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1816 =
                let uu____1819 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1820 =
                  let uu____1823 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____1823; FStar_Format.text "end"]  in
                uu____1819 :: uu____1820  in
              FStar_Format.combine FStar_Format.hardline uu____1816  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1839 =
                let uu____1842 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1843 =
                  let uu____1846 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1851 =
                    let uu____1854 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____1855 =
                      let uu____1858 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____1858; FStar_Format.text "end"]  in
                    uu____1854 :: uu____1855  in
                  uu____1846 :: uu____1851  in
                uu____1842 :: uu____1843  in
              FStar_Format.combine FStar_Format.hardline uu____1839  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____1896 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____1896 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1901 =
              let uu____1904 =
                let uu____1907 =
                  let uu____1908 = ptctor currentModule exn  in
                  FStar_Format.text uu____1908  in
                [uu____1907]  in
              (FStar_Format.text "raise") :: uu____1904  in
            FStar_Format.reduce1 uu____1901
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____1922 =
              let uu____1925 =
                let uu____1928 =
                  let uu____1929 = ptctor currentModule exn  in
                  FStar_Format.text uu____1929  in
                let uu____1930 =
                  let uu____1933 =
                    let uu____1934 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____1934  in
                  [uu____1933]  in
                uu____1928 :: uu____1930  in
              (FStar_Format.text "raise") :: uu____1925  in
            FStar_Format.reduce1 uu____1922
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1957 =
              let uu____1960 =
                let uu____1963 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____1968 =
                  let uu____1971 =
                    let uu____1974 =
                      let uu____1975 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____1975
                       in
                    [uu____1974]  in
                  (FStar_Format.text "with") :: uu____1971  in
                uu____1963 :: uu____1968  in
              (FStar_Format.text "try") :: uu____1960  in
            FStar_Format.combine FStar_Format.hardline uu____1957
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
          let uu____1988 =
            let uu____1999 = as_bin_op p  in FStar_Option.get uu____1999  in
          match uu____1988 with
          | (uu____2022,prio,txt) ->
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
        let uu____2047 =
          let uu____2052 = as_uni_op p  in FStar_Option.get uu____2052  in
        match uu____2047 with
        | (uu____2063,txt) ->
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
          let uu____2074 = string_of_mlconstant c  in
          FStar_Format.text uu____2074
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2101 =
            match uu____2101 with
            | (name,p) ->
                let uu____2108 =
                  let uu____2111 =
                    let uu____2112 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2112  in
                  let uu____2115 =
                    let uu____2118 =
                      let uu____2121 = doc_of_pattern currentModule p  in
                      [uu____2121]  in
                    (FStar_Format.text "=") :: uu____2118  in
                  uu____2111 :: uu____2115  in
                FStar_Format.reduce1 uu____2108
             in
          let uu____2122 =
            let uu____2123 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____2123  in
          FStar_Format.cbrackets uu____2122
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2134 = is_standard_constructor ctor  in
            if uu____2134
            then
              let uu____2135 =
                let uu____2140 = as_standard_constructor ctor  in
                FStar_Option.get uu____2140  in
              FStar_Pervasives_Native.snd uu____2135
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2159 = is_standard_constructor ctor  in
            if uu____2159
            then
              let uu____2160 =
                let uu____2165 = as_standard_constructor ctor  in
                FStar_Option.get uu____2165  in
              FStar_Pervasives_Native.snd uu____2160
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2184 =
                  let uu____2187 =
                    let uu____2188 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____2188  in
                  let uu____2189 =
                    let uu____2192 =
                      let uu____2195 = doc_of_pattern currentModule xs  in
                      [uu____2195]  in
                    (FStar_Format.text "::") :: uu____2192  in
                  uu____2187 :: uu____2189  in
                FStar_Format.reduce uu____2184
            | (uu____2196,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2197)::[]) ->
                let uu____2202 =
                  let uu____2205 =
                    let uu____2208 =
                      let uu____2209 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____2209  in
                    [uu____2208]  in
                  (FStar_Format.text name) :: uu____2205  in
                FStar_Format.reduce1 uu____2202
            | uu____2210 ->
                let uu____2217 =
                  let uu____2220 =
                    let uu____2223 =
                      let uu____2224 =
                        let uu____2225 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2225
                         in
                      FStar_Format.parens uu____2224  in
                    [uu____2223]  in
                  (FStar_Format.text name) :: uu____2220  in
                FStar_Format.reduce1 uu____2217
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____2238 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____2238
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____2249  ->
      match uu____2249 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2258 =
                  let uu____2261 =
                    let uu____2264 = doc_of_pattern currentModule p  in
                    [uu____2264]  in
                  (FStar_Format.text "|") :: uu____2261  in
                FStar_Format.reduce1 uu____2258
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____2271 =
                  let uu____2274 =
                    let uu____2277 = doc_of_pattern currentModule p  in
                    [uu____2277; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____2274  in
                FStar_Format.reduce1 uu____2271
             in
          let uu____2278 =
            let uu____2281 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____2282 =
              let uu____2285 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____2285; FStar_Format.text "end"]  in
            uu____2281 :: uu____2282  in
          FStar_Format.combine FStar_Format.hardline uu____2278

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____2291  ->
      match uu____2291 with
      | (rec_,top_level,lets) ->
          let for1 uu____2310 =
            match uu____2310 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2313;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____2315;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2329 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____2329
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2330::uu____2331,uu____2332) ->
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
                                let uu____2384 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____2384
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____2398 =
                  let uu____2401 =
                    let uu____2404 = FStar_Format.reduce1 ids  in
                    [uu____2404; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____2401  in
                FStar_Format.reduce1 uu____2398
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
  fun uu____2418  ->
    match uu____2418 with
    | (lineno,file) ->
        let uu____2421 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ())
           in
        if uu____2421
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
      let for1 uu____2451 =
        match uu____2451 with
        | (uu____2470,x,mangle_opt,tparams,uu____2474,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2492 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____2500 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____2500
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2524 =
                    match uu____2524 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____2537 =
                    let uu____2538 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2538
                     in
                  FStar_Format.cbrackets uu____2537
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2571 =
                    match uu____2571 with
                    | (name,tys) ->
                        let uu____2596 = FStar_List.split tys  in
                        (match uu____2596 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2615 ->
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
              let uu____2645 =
                let uu____2648 =
                  let uu____2651 =
                    let uu____2652 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____2652  in
                  [uu____2651]  in
                tparams1 :: uu____2648  in
              FStar_Format.reduce1 uu____2645  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____2657 =
                   let uu____2660 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____2660; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____2657)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2683 =
            let uu____2686 =
              let uu____2689 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____2689]  in
            (FStar_Format.text "type") :: uu____2686  in
          FStar_Format.reduce1 uu____2683
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
          let uu____2707 =
            let uu____2710 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____2711 =
              let uu____2714 = doc_of_sig currentModule subsig  in
              let uu____2715 =
                let uu____2718 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____2718]  in
              uu____2714 :: uu____2715  in
            uu____2710 :: uu____2711  in
          FStar_Format.combine FStar_Format.hardline uu____2707
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____2736 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____2736  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2738,ty)) ->
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
            let uu____2806 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____2806  in
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
          let uu____2817 =
            let uu____2820 =
              let uu____2823 =
                let uu____2826 =
                  let uu____2829 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____2829]  in
                (FStar_Format.text "=") :: uu____2826  in
              (FStar_Format.text "_") :: uu____2823  in
            (FStar_Format.text "let") :: uu____2820  in
          FStar_Format.reduce1 uu____2817
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2853 ->
                  FStar_Format.empty
              | uu____2854 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____2863  ->
    match uu____2863 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2929 =
          match uu____2929 with
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
                  (fun uu____3002  ->
                     match uu____3002 with
                     | (s,uu____3008) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____3035 =
                let uu____3038 =
                  let uu____3041 =
                    let uu____3044 = FStar_Format.reduce sub3  in
                    [uu____3044;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3041
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3038
                 in
              FStar_Format.reduce uu____3035
        
        and for1_mod istop uu____3047 =
          match uu____3047 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3115 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)]
                 in
              let head1 =
                let uu____3126 =
                  let uu____3129 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____3129
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
                FStar_Format.reduce1 uu____3126  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____3148  ->
                     match uu____3148 with
                     | (uu____3153,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____3184 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____3184
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____3188 =
                let uu____3191 =
                  let uu____3194 =
                    let uu____3197 =
                      let uu____3200 =
                        let uu____3203 =
                          let uu____3206 = FStar_Format.reduce sub3  in
                          [uu____3206;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3203
                         in
                      FStar_Format.hardline :: uu____3200  in
                    FStar_List.append maybe_open_pervasives uu____3197  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3194
                   in
                FStar_List.append prefix1 uu____3191  in
              FStar_All.pipe_left FStar_Format.reduce uu____3188
         in
        let docs =
          FStar_List.map
            (fun uu____3245  ->
               match uu____3245 with
               | (x,s,m) ->
                   let uu____3295 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____3296 = for1_mod true (x, s, m)  in
                   (uu____3295, uu____3296)) mllib
           in
        docs
  
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3325 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____3325 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3337 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____3337 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  