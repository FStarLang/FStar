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
  
let prim_types : 'uu____1235 . unit -> 'uu____1235 Prims.list =
  fun uu____1239  -> [] 
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
  fun uu____1334  ->
    match uu____1334 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1393  ->
               match uu____1393 with | (y,uu____1409,uu____1410) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1448 = as_bin_op p  in
    uu____1448 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1505  ->
    match uu____1505 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____1533 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____1551  ->
               match uu____1551 with | (y,uu____1560) -> x = y) uu____1533
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1581 = as_uni_op p  in
    uu____1581 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____1625  ->
    match uu____1625 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____1662  ->
               match uu____1662 with | (y,uu____1671) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____1692 = as_standard_constructor p  in
    uu____1692 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) -> (Prims.int * fixity) -> doc -> doc) =
  fun uu____1742  ->
    fun inner  ->
      fun doc  ->
        match uu____1742 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1808 = _inner  in
              match uu____1808 with
              | (pi,fi) ->
                  let uu____1819 = _outer  in
                  (match uu____1819 with
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
                           | (uu____1837,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1839,uu____1840) -> false)))
               in
            if noparens inner outer side then doc else parens doc
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___0_1879  ->
      if uu___0_1879 = 92
      then "\\\\"
      else
        if uu___0_1879 = 32
        then " "
        else
          if uu___0_1879 = 8
          then "\\b"
          else
            if uu___0_1879 = 9
            then "\\t"
            else
              if uu___0_1879 = 13
              then "\\r"
              else
                if uu___0_1879 = 10
                then "\\n"
                else
                  if uu___0_1879 = 39
                  then "\\'"
                  else
                    if uu___0_1879 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___0_1879
                      then FStar_Util.string_of_char uu___0_1879
                      else
                        if FStar_Util.is_punctuation uu___0_1879
                        then FStar_Util.string_of_char uu___0_1879
                        else
                          if FStar_Util.is_symbol uu___0_1879
                          then FStar_Util.string_of_char uu___0_1879
                          else fallback uu___0_1879
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1926 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____1926
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
        (s,FStar_Pervasives_Native.Some (uu____1968,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1982,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____2014 =
          let uu____2016 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____2016 "\""  in
        Prims.op_Hat "\"" uu____2014
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____2022 =
          let uu____2024 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____2024 "\""  in
        Prims.op_Hat "\"" uu____2022
    | uu____2028 ->
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
            let doc =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc1 =
              let uu____2087 =
                let uu____2088 = combine (text " * ") doc  in hbox uu____2088
                 in
              parens uu____2087  in
            doc1
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____2098 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____2104 =
                    let uu____2105 = combine (text ", ") args1  in
                    hbox uu____2105  in
                  parens uu____2104
               in
            let name1 = ptsym currentModule name  in
            let uu____2109 = reduce1 [args1; text name1]  in hbox uu____2109
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2111,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____2115 =
              let uu____2116 = reduce1 [d1; text " -> "; d2]  in
              hbox uu____2116  in
            maybe_paren outer t_prio_fun uu____2115
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____2118 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2118 then text "obj" else text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____2130 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____2130

let rec (doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____2223 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2223
            then
              let uu____2226 = reduce [text "Prims.unsafe_coerce "; doc]  in
              parens uu____2226
            else
              (let uu____2230 = reduce [text "Obj.magic "; parens doc]  in
               parens uu____2230)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map (fun d  -> reduce [d; text ";"; hardline]) docs
               in
            let uu____2244 = reduce docs1  in parens uu____2244
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2246 = string_of_mlconstant c  in text uu____2246
        | FStar_Extraction_ML_Syntax.MLE_Var x -> text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2251 = ptsym currentModule path  in text uu____2251
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2285 =
              match uu____2285 with
              | (name,e1) ->
                  let doc =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2296 =
                    let uu____2299 =
                      let uu____2300 = ptsym currentModule (path, name)  in
                      text uu____2300  in
                    [uu____2299; text "="; doc]  in
                  reduce1 uu____2296
               in
            let uu____2307 =
              let uu____2308 = FStar_List.map for1 fields  in
              combine (text "; ") uu____2308  in
            cbrackets uu____2307
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2322 = is_standard_constructor ctor  in
              if uu____2322
              then
                let uu____2326 =
                  let uu____2333 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2333  in
                FStar_Pervasives_Native.snd uu____2326
              else ptctor currentModule ctor  in
            text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2360 = is_standard_constructor ctor  in
              if uu____2360
              then
                let uu____2364 =
                  let uu____2371 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2371  in
                FStar_Pervasives_Native.snd uu____2364
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc =
              match (name, args1) with
              | ("::",x::xs::[]) -> reduce [parens x; text "::"; xs]
              | (uu____2404,uu____2405) ->
                  let uu____2412 =
                    let uu____2415 =
                      let uu____2418 =
                        let uu____2419 = combine (text ", ") args1  in
                        parens uu____2419  in
                      [uu____2418]  in
                    (text name) :: uu____2415  in
                  reduce1 uu____2412
               in
            maybe_paren outer e_app_prio doc
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2430 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   parens uu____2430) es
               in
            let docs1 =
              let uu____2432 = combine (text ", ") docs  in parens uu____2432
               in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2449 =
                  let uu____2452 =
                    let uu____2455 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2455]  in
                  hardline :: uu____2452  in
                reduce uu____2449
              else empty  in
            let doc = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2464 =
              let uu____2465 =
                let uu____2468 =
                  let uu____2471 =
                    let uu____2474 = reduce1 [text "in"; body1]  in
                    [uu____2474]  in
                  doc :: uu____2471  in
                pre :: uu____2468  in
              combine hardline uu____2465  in
            parens uu____2464
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2485::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2487;
                    FStar_Extraction_ML_Syntax.loc = uu____2488;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2490)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2492;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2493;_}::[])
                 when
                 let uu____2537 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2537 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2563;
                            FStar_Extraction_ML_Syntax.loc = uu____2564;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2566;
                       FStar_Extraction_ML_Syntax.loc = uu____2567;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2625;
                   FStar_Extraction_ML_Syntax.loc = uu____2626;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2639;
                   FStar_Extraction_ML_Syntax.loc = uu____2640;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2647 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2658 = reduce1 (e2 :: args1)  in parens uu____2658)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc =
              let uu____2663 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2663
              then
                reduce [e2; text "."; text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2673 =
                   let uu____2676 =
                     let uu____2679 =
                       let uu____2682 =
                         let uu____2683 = ptsym currentModule f  in
                         text uu____2683  in
                       [uu____2682]  in
                     (text ".") :: uu____2679  in
                   e2 :: uu____2676  in
                 reduce uu____2673)
               in
            doc
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2719 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2719
              then
                let uu____2722 =
                  let uu____2725 =
                    let uu____2728 =
                      let uu____2731 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2733 =
                              let uu____2736 =
                                let uu____2739 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2739]  in
                              (text " : ") :: uu____2736  in
                            reduce1 uu____2733
                        | uu____2741 -> text ""  in
                      [uu____2731; text ")"]  in
                    (text x) :: uu____2728  in
                  (text "(") :: uu____2725  in
                reduce1 uu____2722
              else text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2760  ->
                   match uu____2760 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc =
              let uu____2772 =
                let uu____2775 =
                  let uu____2778 = reduce1 ids1  in
                  [uu____2778; text "->"; body1]  in
                (text "fun") :: uu____2775  in
              reduce1 uu____2772  in
            parens doc
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc =
              let uu____2787 =
                let uu____2790 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2794 =
                  let uu____2797 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2797; text "end"]  in
                uu____2790 :: uu____2794  in
              combine hardline uu____2787  in
            maybe_paren outer e_bin_prio_if doc
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc =
              let uu____2806 =
                let uu____2809 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2813 =
                  let uu____2816 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2817 =
                    let uu____2820 =
                      reduce1 [text "end"; text "else"; text "begin"]  in
                    let uu____2824 =
                      let uu____2827 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2827; text "end"]  in
                    uu____2820 :: uu____2824  in
                  uu____2816 :: uu____2817  in
                uu____2809 :: uu____2813  in
              combine hardline uu____2806  in
            maybe_paren outer e_bin_prio_if doc
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc =
              let uu____2866 =
                reduce1 [text "match"; parens cond1; text "with"]  in
              uu____2866 :: pats1  in
            let doc1 = combine hardline doc  in parens doc1
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2873 =
              let uu____2876 =
                let uu____2879 =
                  let uu____2880 = ptctor currentModule exn  in
                  text uu____2880  in
                [uu____2879]  in
              (text "raise") :: uu____2876  in
            reduce1 uu____2873
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2892 =
              let uu____2895 =
                let uu____2898 =
                  let uu____2899 = ptctor currentModule exn  in
                  text uu____2899  in
                let uu____2901 =
                  let uu____2904 =
                    let uu____2905 = combine (text ", ") args1  in
                    parens uu____2905  in
                  [uu____2904]  in
                uu____2898 :: uu____2901  in
              (text "raise") :: uu____2895  in
            reduce1 uu____2892
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2930 =
              let uu____2933 =
                let uu____2936 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2937 =
                  let uu____2940 =
                    let uu____2943 =
                      let uu____2944 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      combine hardline uu____2944  in
                    [uu____2943]  in
                  (text "with") :: uu____2940  in
                uu____2936 :: uu____2937  in
              (text "try") :: uu____2933  in
            combine hardline uu____2930
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
          let uu____2968 =
            let uu____2982 = as_bin_op p  in FStar_Option.get uu____2982  in
          match uu____2968 with
          | (uu____3011,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc = reduce1 [e11; text txt; e21]  in parens doc

and (doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____3035 =
          let uu____3042 = as_uni_op p  in FStar_Option.get uu____3042  in
        match uu____3035 with
        | (uu____3057,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc = reduce1 [text txt; parens e11]  in parens doc

and (doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> doc)
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____3070 = string_of_mlconstant c  in text uu____3070
      | FStar_Extraction_ML_Syntax.MLP_Var x -> text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____3106 =
            match uu____3106 with
            | (name,p) ->
                let uu____3116 =
                  let uu____3119 =
                    let uu____3120 = ptsym currentModule (path, name)  in
                    text uu____3120  in
                  let uu____3126 =
                    let uu____3129 =
                      let uu____3132 = doc_of_pattern currentModule p  in
                      [uu____3132]  in
                    (text "=") :: uu____3129  in
                  uu____3119 :: uu____3126  in
                reduce1 uu____3116
             in
          let uu____3134 =
            let uu____3135 = FStar_List.map for1 fields  in
            combine (text "; ") uu____3135  in
          cbrackets uu____3134
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____3149 = is_standard_constructor ctor  in
            if uu____3149
            then
              let uu____3153 =
                let uu____3160 = as_standard_constructor ctor  in
                FStar_Option.get uu____3160  in
              FStar_Pervasives_Native.snd uu____3153
            else ptctor currentModule ctor  in
          text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3187 = is_standard_constructor ctor  in
            if uu____3187
            then
              let uu____3191 =
                let uu____3198 = as_standard_constructor ctor  in
                FStar_Option.get uu____3198  in
              FStar_Pervasives_Native.snd uu____3191
            else ptctor currentModule ctor  in
          let doc =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3227 =
                  let uu____3230 =
                    let uu____3231 = doc_of_pattern currentModule x  in
                    parens uu____3231  in
                  let uu____3232 =
                    let uu____3235 =
                      let uu____3238 = doc_of_pattern currentModule xs  in
                      [uu____3238]  in
                    (text "::") :: uu____3235  in
                  uu____3230 :: uu____3232  in
                reduce uu____3227
            | (uu____3240,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3241)::[]) ->
                let uu____3248 =
                  let uu____3251 =
                    let uu____3254 =
                      let uu____3255 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3255  in
                    [uu____3254]  in
                  (text name) :: uu____3251  in
                reduce1 uu____3248
            | uu____3256 ->
                let uu____3264 =
                  let uu____3267 =
                    let uu____3270 =
                      let uu____3271 =
                        let uu____3272 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        combine (text ", ") uu____3272  in
                      parens uu____3271  in
                    [uu____3270]  in
                  (text name) :: uu____3267  in
                reduce1 uu____3264
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3287 = combine (text ", ") ps1  in parens uu____3287
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map parens ps1  in combine (text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> doc)
  =
  fun currentModule  ->
    fun uu____3300  ->
      match uu____3300 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3310 =
                  let uu____3313 =
                    let uu____3316 = doc_of_pattern currentModule p  in
                    [uu____3316]  in
                  (text "|") :: uu____3313  in
                reduce1 uu____3310
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3320 =
                  let uu____3323 =
                    let uu____3326 = doc_of_pattern currentModule p  in
                    [uu____3326; text "when"; c1]  in
                  (text "|") :: uu____3323  in
                reduce1 uu____3320
             in
          let uu____3329 =
            let uu____3332 = reduce1 [case; text "->"; text "begin"]  in
            let uu____3335 =
              let uu____3338 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3338; text "end"]  in
            uu____3332 :: uu____3335  in
          combine hardline uu____3329

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> doc)
  =
  fun currentModule  ->
    fun uu____3341  ->
      match uu____3341 with
      | (rec_,top_level,lets) ->
          let for1 uu____3366 =
            match uu____3366 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3369;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3371;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then text ""
                  else
                    (let uu____3387 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3387
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3390::uu____3391,uu____3392) -> text ""
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
                                let uu____3416 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3416 reduce1  in
                              reduce1 [text ":"; vars; text "."; ty1])
                       else text "")
                   in
                let uu____3435 =
                  let uu____3438 =
                    let uu____3441 = reduce1 ids  in
                    [uu____3441; ty_annot; text "="; e1]  in
                  (text name) :: uu____3438  in
                reduce1 uu____3435
             in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then reduce1 [text "let"; text "rec"]
            else text "let"  in
          let lets1 = FStar_List.map for1 lets  in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc  ->
                   reduce1
                     [if i = Prims.int_zero then letdoc else text "and"; doc])
              lets1
             in
          combine hardline lets2

and (doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> doc) =
  fun uu____3467  ->
    match uu____3467 with
    | (lineno,file) ->
        let uu____3474 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3474
        then empty
        else
          (let file1 = FStar_Util.basename file  in
           let uu____3483 =
             let uu____3486 =
               let uu____3489 = num lineno  in
               [uu____3489;
               text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))]  in
             (text "#") :: uu____3486  in
           reduce1 uu____3483)

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____3533 =
        match uu____3533 with
        | (uu____3556,x,mangle_opt,tparams,uu____3560,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> empty
              | x2::[] -> text x2
              | uu____3595 ->
                  let doc = FStar_List.map (fun x2  -> text x2) tparams  in
                  let uu____3606 = combine (text ", ") doc  in
                  parens uu____3606
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3633 =
                    match uu____3633 with
                    | (name,ty) ->
                        let name1 = text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        reduce1 [name1; text ":"; ty1]
                     in
                  let uu____3646 =
                    let uu____3647 = FStar_List.map forfield fields  in
                    combine (text "; ") uu____3647  in
                  cbrackets uu____3646
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3688 =
                    match uu____3688 with
                    | (name,tys) ->
                        let uu____3719 = FStar_List.split tys  in
                        (match uu____3719 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> text name
                              | uu____3742 ->
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
            let doc =
              let uu____3773 =
                let uu____3776 =
                  let uu____3779 =
                    let uu____3780 = ptsym currentModule ([], x1)  in
                    text uu____3780  in
                  [uu____3779]  in
                tparams1 :: uu____3776  in
              reduce1 uu____3773  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3789 =
                   let uu____3792 = reduce1 [doc; text "="]  in
                   [uu____3792; body2]  in
                 combine hardline uu____3789)
         in
      let doc = FStar_List.map for1 decls  in
      let doc1 =
        if (FStar_List.length doc) > Prims.int_zero
        then
          let uu____3800 =
            let uu____3803 =
              let uu____3806 = combine (text " \n and ") doc  in [uu____3806]
               in
            (text "type") :: uu____3803  in
          reduce1 uu____3800
        else text ""  in
      doc1
  
let rec (doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> doc)
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____3842 =
            let uu____3845 = reduce1 [text "module"; text x; text "="]  in
            let uu____3848 =
              let uu____3851 = doc_of_sig currentModule subsig  in
              let uu____3852 =
                let uu____3855 = reduce1 [text "end"]  in [uu____3855]  in
              uu____3851 :: uu____3852  in
            uu____3845 :: uu____3848  in
          combine hardline uu____3842
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3875 = combine (text " * ") args1  in parens uu____3875
             in
          reduce1 [text "exception"; text x; text "of"; args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3880,ty)) ->
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
            let uu____3959 = combine (text " * ") args2  in parens uu____3959
             in
          reduce1 [text "exception"; text x; text "of"; args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____3975 =
            let uu____3978 =
              let uu____3981 =
                let uu____3984 =
                  let uu____3987 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____3987]  in
                (text "=") :: uu____3984  in
              (text "_") :: uu____3981  in
            (text "let") :: uu____3978  in
          reduce1 uu____3975
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
             let doc = doc_of_mod1 currentModule x  in
             [doc;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____4017 -> empty
              | uu____4018 -> hardline);
             hardline]) m
         in
      reduce (FStar_List.flatten docs)
  
let (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun uu____4031  ->
    match uu____4031 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____4101 =
          match uu____4101 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head1 =
                reduce1 [text "module"; text x1; text ":"; text "sig"]  in
              let tail1 = reduce1 [text "end"]  in
              let doc =
                FStar_Option.map
                  (fun uu____4161  ->
                     match uu____4161 with
                     | (s,uu____4167) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map (fun x2  -> reduce [x2; hardline; hardline])
                  sub2
                 in
              let uu____4188 =
                let uu____4191 =
                  let uu____4194 =
                    let uu____4197 = reduce sub3  in
                    [uu____4197; cat tail1 hardline]  in
                  (match doc with
                   | FStar_Pervasives_Native.None  -> empty
                   | FStar_Pervasives_Native.Some s -> cat s hardline) ::
                    uu____4194
                   in
                (cat head1 hardline) :: uu____4191  in
              reduce uu____4188
        
        and for1_mod istop uu____4200 =
          match uu____4200 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4282 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [hardline; text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____4303 =
                  let uu____4306 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4306
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
                reduce1 uu____4303  in
              let tail1 =
                if Prims.op_Negation istop
                then reduce1 [text "end"]
                else reduce1 []  in
              let doc =
                FStar_Option.map
                  (fun uu____4337  ->
                     match uu____4337 with
                     | (uu____4342,m) -> doc_of_mod target_mod_name m) sigmod
                 in
              let sub2 = FStar_List.map (for1_mod false) sub1  in
              let sub3 =
                FStar_List.map (fun x  -> reduce [x; hardline; hardline])
                  sub2
                 in
              let prefix1 =
                let uu____4368 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4368
                then [cat (text "#light \"off\"") hardline]
                else []  in
              let uu____4376 =
                let uu____4379 =
                  let uu____4382 =
                    let uu____4385 =
                      let uu____4388 =
                        let uu____4391 =
                          let uu____4394 = reduce sub3  in
                          [uu____4394; cat tail1 hardline]  in
                        (match doc with
                         | FStar_Pervasives_Native.None  -> empty
                         | FStar_Pervasives_Native.Some s -> cat s hardline)
                          :: uu____4391
                         in
                      hardline :: uu____4388  in
                    FStar_List.append maybe_open_pervasives uu____4385  in
                  FStar_List.append [head1; hardline; text "open Prims"]
                    uu____4382
                   in
                FStar_List.append prefix1 uu____4379  in
              FStar_All.pipe_left reduce uu____4376
         in
        let docs =
          FStar_List.map
            (fun uu____4438  ->
               match uu____4438 with
               | (x,s,m) ->
                   let uu____4495 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4497 = for1_mod true (x, s, m)  in
                   (uu____4495, uu____4497)) mllib
           in
        docs
  
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____4526  -> match uu____4526 with | Doc doc -> doc 
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc =
        let uu____4557 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4557 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc =
        let uu____4573 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4573 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc
  