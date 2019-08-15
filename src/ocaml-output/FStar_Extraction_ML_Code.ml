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
  ((Prims.of_int (10)), (Infix Right)) 
let (t_prio_tpl : (Prims.int * fixity)) =
  ((Prims.of_int (20)), (Infix NonAssoc)) 
let (t_prio_name : (Prims.int * fixity)) = ((Prims.of_int (30)), Postfix) 
let (e_bin_prio_lambda : (Prims.int * fixity)) = ((Prims.of_int (5)), Prefix) 
let (e_bin_prio_if : (Prims.int * fixity)) = ((Prims.of_int (15)), Prefix) 
let (e_bin_prio_letin : (Prims.int * fixity)) = ((Prims.of_int (19)), Prefix) 
let (e_bin_prio_or : (Prims.int * fixity)) =
  ((Prims.of_int (20)), (Infix Left)) 
let (e_bin_prio_and : (Prims.int * fixity)) =
  ((Prims.of_int (25)), (Infix Left)) 
let (e_bin_prio_eq : (Prims.int * fixity)) =
  ((Prims.of_int (27)), (Infix NonAssoc)) 
let (e_bin_prio_order : (Prims.int * fixity)) =
  ((Prims.of_int (29)), (Infix NonAssoc)) 
let (e_bin_prio_op1 : (Prims.int * fixity)) =
  ((Prims.of_int (30)), (Infix Left)) 
let (e_bin_prio_op2 : (Prims.int * fixity)) =
  ((Prims.of_int (40)), (Infix Left)) 
let (e_bin_prio_op3 : (Prims.int * fixity)) =
  ((Prims.of_int (50)), (Infix Left)) 
let (e_bin_prio_op4 : (Prims.int * fixity)) =
  ((Prims.of_int (60)), (Infix Left)) 
let (e_bin_prio_comb : (Prims.int * fixity)) =
  ((Prims.of_int (70)), (Infix Left)) 
let (e_bin_prio_seq : (Prims.int * fixity)) =
  ((Prims.of_int (100)), (Infix Left)) 
let (e_app_prio : (Prims.int * fixity)) =
  ((Prims.of_int (10000)), (Infix Left)) 
let (min_op_prec : (Prims.int * fixity)) =
  ((~- Prims.int_one), (Infix NonAssoc)) 
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
  fun i  -> let uu____305 = FStar_Util.string_of_int i  in Doc uu____305 
let (break1 : doc) = text " " 
let (enclose : doc -> doc -> doc -> doc) =
  fun uu____322  ->
    fun uu____323  ->
      fun uu____324  ->
        match (uu____322, uu____323, uu____324) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.op_Hat l (Prims.op_Hat x r))
  
let (cbrackets : doc -> doc) =
  fun uu____336  ->
    match uu____336 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____346  ->
    match uu____346 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____360  ->
    fun uu____361  ->
      match (uu____360, uu____361) with
      | (Doc d1,Doc d2) -> Doc (Prims.op_Hat d1 d2)
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____387  ->
    fun docs  ->
      match uu____387 with
      | Doc sep ->
          let select uu____401 =
            match uu____401 with
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
    | ([],uu____466) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____490,uu____491) -> false
  
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
                  let uu____572 = FStar_Util.first_N cg_len ns  in
                  match uu____572 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____612 =
                           let uu____616 =
                             let uu____620 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____620]  in
                           FStar_List.append pfx uu____616  in
                         FStar_Pervasives_Native.Some uu____612
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
      let uu____666 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____666 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____682 ->
          let uu____684 = x  in
          (match uu____684 with
           | (ns,x1) ->
               let uu____695 = path_of_ns currentModule ns  in
               (uu____695, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____713 =
      let uu____715 =
        let uu____717 = FStar_String.get s Prims.int_zero  in
        FStar_Char.lowercase uu____717  in
      let uu____720 = FStar_String.get s Prims.int_zero  in
      uu____715 <> uu____720  in
    if uu____713 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____756 = mlpath_of_mlpath currentModule mlp  in
         match uu____756 with
         | (p,s) ->
             let uu____768 =
               let uu____772 =
                 let uu____776 = ptsym_of_symbol s  in [uu____776]  in
               FStar_List.append p uu____772  in
             FStar_String.concat "." uu____768)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____797 = mlpath_of_mlpath currentModule mlp  in
      match uu____797 with
      | (p,s) ->
          let s1 =
            let uu____811 =
              let uu____813 =
                let uu____815 = FStar_String.get s Prims.int_zero  in
                FStar_Char.uppercase uu____815  in
              let uu____818 = FStar_String.get s Prims.int_zero  in
              uu____813 <> uu____818  in
            if uu____811 then Prims.op_Hat "U__" s else s  in
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
  fun uu____1181  ->
    let op_minus =
      let uu____1184 =
        let uu____1186 = FStar_Options.codegen ()  in
        uu____1186 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____1184 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____1235 . unit -> 'Auu____1235 Prims.list =
  fun uu____1238  -> [] 
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
  fun uu____1333  ->
    match uu____1333 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1392  ->
               match uu____1392 with | (y,uu____1408,uu____1409) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1447 = as_bin_op p  in
    uu____1447 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1504  ->
    match uu____1504 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____1532 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____1550  ->
               match uu____1550 with | (y,uu____1559) -> x = y) uu____1532
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1580 = as_uni_op p  in
    uu____1580 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1624  ->
    match uu____1624 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1661  ->
               match uu____1661 with | (y,uu____1670) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1691 = as_standard_constructor p  in
    uu____1691 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) -> (Prims.int * fixity) -> doc -> doc) =
  fun uu____1741  ->
    fun inner  ->
      fun doc1  ->
        match uu____1741 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1807 = _inner  in
              match uu____1807 with
              | (pi,fi) ->
                  let uu____1818 = _outer  in
                  (match uu____1818 with
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
                           | (uu____1836,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1838,uu____1839) -> false)))
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
    fun uu___0_1880  ->
      if uu___0_1880 = 92
      then "\\\\"
      else
        if uu___0_1880 = 32
        then " "
        else
          if uu___0_1880 = 8
          then "\\b"
          else
            if uu___0_1880 = 9
            then "\\t"
            else
              if uu___0_1880 = 13
              then "\\r"
              else
                if uu___0_1880 = 10
                then "\\n"
                else
                  if uu___0_1880 = 39
                  then "\\'"
                  else
                    if uu___0_1880 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___0_1880
                      then FStar_Util.string_of_char uu___0_1880
                      else
                        if FStar_Util.is_punctuation uu___0_1880
                        then FStar_Util.string_of_char uu___0_1880
                        else
                          if FStar_Util.is_symbol uu___0_1880
                          then FStar_Util.string_of_char uu___0_1880
                          else fallback uu___0_1880
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1927 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____1927
          (if
             ((nc >= (Prims.of_int (32))) && (nc <= (Prims.of_int (127)))) &&
               (nc <> (Prims.of_int (34)))
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
        (s,FStar_Pervasives_Native.Some (uu____1969,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1983,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____2016 =
          let uu____2018 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____2018 "\""  in
        Prims.op_Hat "\"" uu____2016
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____2024 =
          let uu____2026 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____2026 "\""  in
        Prims.op_Hat "\"" uu____2024
    | uu____2030 ->
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
              let uu____2089 =
                let uu____2090 = combine (text " * ") doc1  in
                hbox uu____2090  in
              parens uu____2089  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____2100 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____2106 =
                    let uu____2107 = combine (text ", ") args1  in
                    hbox uu____2107  in
                  parens uu____2106
               in
            let name1 = ptsym currentModule name  in
            let uu____2111 = reduce1 [args1; text name1]  in hbox uu____2111
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2113,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____2117 =
              let uu____2118 = reduce1 [d1; text " -> "; d2]  in
              hbox uu____2118  in
            maybe_paren outer t_prio_fun uu____2117
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____2120 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2120 then text "obj" else text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____2132 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____2132

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
            let uu____2225 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2225
            then
              let uu____2228 = reduce [text "Prims.unsafe_coerce "; doc1]  in
              parens uu____2228
            else
              (let uu____2232 = reduce [text "Obj.magic "; parens doc1]  in
               parens uu____2232)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map (fun d  -> reduce [d; text ";"; hardline]) docs
               in
            let uu____2246 = reduce docs1  in parens uu____2246
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2248 = string_of_mlconstant c  in text uu____2248
        | FStar_Extraction_ML_Syntax.MLE_Var x -> text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2253 = ptsym currentModule path  in text uu____2253
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2287 =
              match uu____2287 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2298 =
                    let uu____2301 =
                      let uu____2302 = ptsym currentModule (path, name)  in
                      text uu____2302  in
                    [uu____2301; text "="; doc1]  in
                  reduce1 uu____2298
               in
            let uu____2309 =
              let uu____2310 = FStar_List.map for1 fields  in
              combine (text "; ") uu____2310  in
            cbrackets uu____2309
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2324 = is_standard_constructor ctor  in
              if uu____2324
              then
                let uu____2328 =
                  let uu____2335 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2335  in
                FStar_Pervasives_Native.snd uu____2328
              else ptctor currentModule ctor  in
            text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor_name,arg::[]) when
            FStar_Extraction_ML_Util.is_machine_int ctor_name ->
            let mlp =
              let uu____2359 =
                let uu____2360 =
                  FStar_Extraction_ML_Util.maybe_map_machine_int_constructor
                    ctor_name
                   in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2360  in
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top uu____2359
               in
            doc_of_expr currentModule outer
              (let uu___302_2362 = e  in
               {
                 FStar_Extraction_ML_Syntax.expr =
                   (FStar_Extraction_ML_Syntax.MLE_App (mlp, [arg]));
                 FStar_Extraction_ML_Syntax.mlty =
                   (uu___302_2362.FStar_Extraction_ML_Syntax.mlty);
                 FStar_Extraction_ML_Syntax.loc =
                   (uu___302_2362.FStar_Extraction_ML_Syntax.loc)
               })
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2373 = is_standard_constructor ctor  in
              if uu____2373
              then
                let uu____2377 =
                  let uu____2384 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2384  in
                FStar_Pervasives_Native.snd uu____2377
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) -> reduce [parens x; text "::"; xs]
              | (uu____2417,uu____2418) ->
                  let uu____2425 =
                    let uu____2428 =
                      let uu____2431 =
                        let uu____2432 = combine (text ", ") args1  in
                        parens uu____2432  in
                      [uu____2431]  in
                    (text name) :: uu____2428  in
                  reduce1 uu____2425
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2443 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   parens uu____2443) es
               in
            let docs1 =
              let uu____2445 = combine (text ", ") docs  in parens uu____2445
               in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2462 =
                  let uu____2465 =
                    let uu____2468 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2468]  in
                  hardline :: uu____2465  in
                reduce uu____2462
              else empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2477 =
              let uu____2478 =
                let uu____2481 =
                  let uu____2484 =
                    let uu____2487 = reduce1 [text "in"; body1]  in
                    [uu____2487]  in
                  doc1 :: uu____2484  in
                pre :: uu____2481  in
              combine hardline uu____2478  in
            parens uu____2477
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2498::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2500;
                    FStar_Extraction_ML_Syntax.loc = uu____2501;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2503)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2505;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2506;_}::[])
                 when
                 let uu____2550 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2550 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2576;
                            FStar_Extraction_ML_Syntax.loc = uu____2577;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2579;
                       FStar_Extraction_ML_Syntax.loc = uu____2580;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2638;
                   FStar_Extraction_ML_Syntax.loc = uu____2639;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2652;
                   FStar_Extraction_ML_Syntax.loc = uu____2653;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2660 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2671 = reduce1 (e2 :: args1)  in parens uu____2671)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____2676 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2676
              then
                reduce [e2; text "."; text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2686 =
                   let uu____2689 =
                     let uu____2692 =
                       let uu____2695 =
                         let uu____2696 = ptsym currentModule f  in
                         text uu____2696  in
                       [uu____2695]  in
                     (text ".") :: uu____2692  in
                   e2 :: uu____2689  in
                 reduce uu____2686)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2732 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2732
              then
                let uu____2735 =
                  let uu____2738 =
                    let uu____2741 =
                      let uu____2744 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2746 =
                              let uu____2749 =
                                let uu____2752 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2752]  in
                              (text " : ") :: uu____2749  in
                            reduce1 uu____2746
                        | uu____2754 -> text ""  in
                      [uu____2744; text ")"]  in
                    (text x) :: uu____2741  in
                  (text "(") :: uu____2738  in
                reduce1 uu____2735
              else text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2773  ->
                   match uu____2773 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____2785 =
                let uu____2788 =
                  let uu____2791 = reduce1 ids1  in
                  [uu____2791; text "->"; body1]  in
                (text "fun") :: uu____2788  in
              reduce1 uu____2785  in
            parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2800 =
                let uu____2803 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2807 =
                  let uu____2810 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2810; text "end"]  in
                uu____2803 :: uu____2807  in
              combine hardline uu____2800  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2819 =
                let uu____2822 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2826 =
                  let uu____2829 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2830 =
                    let uu____2833 =
                      reduce1 [text "end"; text "else"; text "begin"]  in
                    let uu____2837 =
                      let uu____2840 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2840; text "end"]  in
                    uu____2833 :: uu____2837  in
                  uu____2829 :: uu____2830  in
                uu____2822 :: uu____2826  in
              combine hardline uu____2819  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2879 =
                reduce1 [text "match"; parens cond1; text "with"]  in
              uu____2879 :: pats1  in
            let doc2 = combine hardline doc1  in parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2886 =
              let uu____2889 =
                let uu____2892 =
                  let uu____2893 = ptctor currentModule exn  in
                  text uu____2893  in
                [uu____2892]  in
              (text "raise") :: uu____2889  in
            reduce1 uu____2886
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2905 =
              let uu____2908 =
                let uu____2911 =
                  let uu____2912 = ptctor currentModule exn  in
                  text uu____2912  in
                let uu____2914 =
                  let uu____2917 =
                    let uu____2918 = combine (text ", ") args1  in
                    parens uu____2918  in
                  [uu____2917]  in
                uu____2911 :: uu____2914  in
              (text "raise") :: uu____2908  in
            reduce1 uu____2905
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2943 =
              let uu____2946 =
                let uu____2949 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2950 =
                  let uu____2953 =
                    let uu____2956 =
                      let uu____2957 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      combine hardline uu____2957  in
                    [uu____2956]  in
                  (text "with") :: uu____2953  in
                uu____2949 :: uu____2950  in
              (text "try") :: uu____2946  in
            combine hardline uu____2943
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
          let uu____2981 =
            let uu____2995 = as_bin_op p  in FStar_Option.get uu____2995  in
          match uu____2981 with
          | (uu____3024,prio,txt) ->
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
        let uu____3048 =
          let uu____3055 = as_uni_op p  in FStar_Option.get uu____3055  in
        match uu____3048 with
        | (uu____3070,txt) ->
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
          let uu____3083 = string_of_mlconstant c  in text uu____3083
      | FStar_Extraction_ML_Syntax.MLP_Var x -> text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____3119 =
            match uu____3119 with
            | (name,p) ->
                let uu____3129 =
                  let uu____3132 =
                    let uu____3133 = ptsym currentModule (path, name)  in
                    text uu____3133  in
                  let uu____3139 =
                    let uu____3142 =
                      let uu____3145 = doc_of_pattern currentModule p  in
                      [uu____3145]  in
                    (text "=") :: uu____3142  in
                  uu____3132 :: uu____3139  in
                reduce1 uu____3129
             in
          let uu____3147 =
            let uu____3148 = FStar_List.map for1 fields  in
            combine (text "; ") uu____3148  in
          cbrackets uu____3147
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____3162 = is_standard_constructor ctor  in
            if uu____3162
            then
              let uu____3166 =
                let uu____3173 = as_standard_constructor ctor  in
                FStar_Option.get uu____3173  in
              FStar_Pervasives_Native.snd uu____3166
            else ptctor currentModule ctor  in
          text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3200 = is_standard_constructor ctor  in
            if uu____3200
            then
              let uu____3204 =
                let uu____3211 = as_standard_constructor ctor  in
                FStar_Option.get uu____3211  in
              FStar_Pervasives_Native.snd uu____3204
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3240 =
                  let uu____3243 =
                    let uu____3244 = doc_of_pattern currentModule x  in
                    parens uu____3244  in
                  let uu____3245 =
                    let uu____3248 =
                      let uu____3251 = doc_of_pattern currentModule xs  in
                      [uu____3251]  in
                    (text "::") :: uu____3248  in
                  uu____3243 :: uu____3245  in
                reduce uu____3240
            | (uu____3253,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3254)::[]) ->
                let uu____3261 =
                  let uu____3264 =
                    let uu____3267 =
                      let uu____3268 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3268  in
                    [uu____3267]  in
                  (text name) :: uu____3264  in
                reduce1 uu____3261
            | uu____3269 ->
                let uu____3277 =
                  let uu____3280 =
                    let uu____3283 =
                      let uu____3284 =
                        let uu____3285 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        combine (text ", ") uu____3285  in
                      parens uu____3284  in
                    [uu____3283]  in
                  (text name) :: uu____3280  in
                reduce1 uu____3277
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3300 = combine (text ", ") ps1  in parens uu____3300
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map parens ps1  in combine (text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> doc)
  =
  fun currentModule  ->
    fun uu____3313  ->
      match uu____3313 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3323 =
                  let uu____3326 =
                    let uu____3329 = doc_of_pattern currentModule p  in
                    [uu____3329]  in
                  (text "|") :: uu____3326  in
                reduce1 uu____3323
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3333 =
                  let uu____3336 =
                    let uu____3339 = doc_of_pattern currentModule p  in
                    [uu____3339; text "when"; c1]  in
                  (text "|") :: uu____3336  in
                reduce1 uu____3333
             in
          let uu____3342 =
            let uu____3345 = reduce1 [case; text "->"; text "begin"]  in
            let uu____3348 =
              let uu____3351 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3351; text "end"]  in
            uu____3345 :: uu____3348  in
          combine hardline uu____3342

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> doc)
  =
  fun currentModule  ->
    fun uu____3354  ->
      match uu____3354 with
      | (rec_,top_level,lets) ->
          let for1 uu____3379 =
            match uu____3379 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3382;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3384;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then text ""
                  else
                    (let uu____3400 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3400
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3403::uu____3404,uu____3405) -> text ""
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
                                let uu____3429 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3429 reduce1  in
                              reduce1 [text ":"; vars; text "."; ty1])
                       else text "")
                   in
                let uu____3448 =
                  let uu____3451 =
                    let uu____3454 = reduce1 ids  in
                    [uu____3454; ty_annot; text "="; e1]  in
                  (text name) :: uu____3451  in
                reduce1 uu____3448
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
                     [if i = Prims.int_zero then letdoc else text "and";
                     doc1]) lets1
             in
          combine hardline lets2

and (doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> doc) =
  fun uu____3480  ->
    match uu____3480 with
    | (lineno,file) ->
        let uu____3487 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3487
        then empty
        else
          (let file1 = FStar_Util.basename file  in
           let uu____3496 =
             let uu____3499 =
               let uu____3502 = num lineno  in
               [uu____3502;
               text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))]  in
             (text "#") :: uu____3499  in
           reduce1 uu____3496)

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____3546 =
        match uu____3546 with
        | (uu____3569,x,mangle_opt,tparams,uu____3573,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> empty
              | x2::[] -> text x2
              | uu____3608 ->
                  let doc1 = FStar_List.map (fun x2  -> text x2) tparams  in
                  let uu____3619 = combine (text ", ") doc1  in
                  parens uu____3619
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3646 =
                    match uu____3646 with
                    | (name,ty) ->
                        let name1 = text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        reduce1 [name1; text ":"; ty1]
                     in
                  let uu____3659 =
                    let uu____3660 = FStar_List.map forfield fields  in
                    combine (text "; ") uu____3660  in
                  cbrackets uu____3659
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3701 =
                    match uu____3701 with
                    | (name,tys) ->
                        let uu____3732 = FStar_List.split tys  in
                        (match uu____3732 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> text name
                              | uu____3755 ->
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
              let uu____3786 =
                let uu____3789 =
                  let uu____3792 =
                    let uu____3793 = ptsym currentModule ([], x1)  in
                    text uu____3793  in
                  [uu____3792]  in
                tparams1 :: uu____3789  in
              reduce1 uu____3786  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3802 =
                   let uu____3805 = reduce1 [doc1; text "="]  in
                   [uu____3805; body2]  in
                 combine hardline uu____3802)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > Prims.int_zero
        then
          let uu____3813 =
            let uu____3816 =
              let uu____3819 = combine (text " \n and ") doc1  in
              [uu____3819]  in
            (text "type") :: uu____3816  in
          reduce1 uu____3813
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
          let uu____3855 =
            let uu____3858 = reduce1 [text "module"; text x; text "="]  in
            let uu____3861 =
              let uu____3864 = doc_of_sig currentModule subsig  in
              let uu____3865 =
                let uu____3868 = reduce1 [text "end"]  in [uu____3868]  in
              uu____3864 :: uu____3865  in
            uu____3858 :: uu____3861  in
          combine hardline uu____3855
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3888 = combine (text " * ") args1  in parens uu____3888
             in
          reduce1 [text "exception"; text x; text "of"; args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3893,ty)) ->
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
            let uu____3972 = combine (text " * ") args2  in parens uu____3972
             in
          reduce1 [text "exception"; text x; text "of"; args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____3988 =
            let uu____3991 =
              let uu____3994 =
                let uu____3997 =
                  let uu____4000 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____4000]  in
                (text "=") :: uu____3997  in
              (text "_") :: uu____3994  in
            (text "let") :: uu____3991  in
          reduce1 uu____3988
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____4030 -> empty
              | uu____4031 -> hardline);
             hardline]) m
         in
      reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun uu____4044  ->
    match uu____4044 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____4114 =
          match uu____4114 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head1 =
                reduce1 [text "module"; text x1; text ":"; text "sig"]  in
              let tail1 = reduce1 [text "end"]  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4174  ->
                     match uu____4174 with
                     | (s,uu____4180) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map (fun x2  -> reduce [x2; hardline; hardline])
                  sub2
                 in
              let uu____4201 =
                let uu____4204 =
                  let uu____4207 =
                    let uu____4210 = reduce sub3  in
                    [uu____4210; cat tail1 hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> empty
                   | FStar_Pervasives_Native.Some s -> cat s hardline) ::
                    uu____4207
                   in
                (cat head1 hardline) :: uu____4204  in
              reduce uu____4201
        
        and for1_mod istop uu____4213 =
          match uu____4213 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4295 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [hardline; text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____4316 =
                  let uu____4319 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4319
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
                reduce1 uu____4316  in
              let tail1 =
                if Prims.op_Negation istop
                then reduce1 [text "end"]
                else reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4350  ->
                     match uu____4350 with
                     | (uu____4355,m) -> doc_of_mod target_mod_name m) sigmod
                 in
              let sub2 = FStar_List.map (for1_mod false) sub1  in
              let sub3 =
                FStar_List.map (fun x  -> reduce [x; hardline; hardline])
                  sub2
                 in
              let prefix1 =
                let uu____4381 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4381
                then [cat (text "#light \"off\"") hardline]
                else []  in
              let uu____4389 =
                let uu____4392 =
                  let uu____4395 =
                    let uu____4398 =
                      let uu____4401 =
                        let uu____4404 =
                          let uu____4407 = reduce sub3  in
                          [uu____4407; cat tail1 hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  -> empty
                         | FStar_Pervasives_Native.Some s -> cat s hardline)
                          :: uu____4404
                         in
                      hardline :: uu____4401  in
                    FStar_List.append maybe_open_pervasives uu____4398  in
                  FStar_List.append [head1; hardline; text "open Prims"]
                    uu____4395
                   in
                FStar_List.append prefix1 uu____4392  in
              FStar_All.pipe_left reduce uu____4389
         in
        let docs =
          FStar_List.map
            (fun uu____4451  ->
               match uu____4451 with
               | (x,s,m) ->
                   let uu____4508 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4510 = for1_mod true (x, s, m)  in
                   (uu____4508, uu____4510)) mllib
           in
        docs
  
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____4539  -> match uu____4539 with | Doc doc1 -> doc1 
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
        let uu____4570 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4570 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____4586 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4586 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc1
  