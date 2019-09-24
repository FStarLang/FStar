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
    fun uu___0_1878  ->
      if uu___0_1878 = 92
      then "\\\\"
      else
        if uu___0_1878 = 32
        then " "
        else
          if uu___0_1878 = 8
          then "\\b"
          else
            if uu___0_1878 = 9
            then "\\t"
            else
              if uu___0_1878 = 13
              then "\\r"
              else
                if uu___0_1878 = 10
                then "\\n"
                else
                  if uu___0_1878 = 39
                  then "\\'"
                  else
                    if uu___0_1878 = 34
                    then "\\\""
                    else
                      (let uu____1916 =
                         FStar_Util.is_letter_or_digit uu___0_1878  in
                       if uu____1916
                       then FStar_Util.string_of_char uu___0_1878
                       else
                         (let uu____1919 =
                            FStar_Util.is_punctuation uu___0_1878  in
                          if uu____1919
                          then FStar_Util.string_of_char uu___0_1878
                          else
                            (let uu____1922 =
                               FStar_Util.is_symbol uu___0_1878  in
                             if uu____1922
                             then FStar_Util.string_of_char uu___0_1878
                             else fallback uu___0_1878)))
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1941 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____1941
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
        (s,FStar_Pervasives_Native.Some (uu____1983,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1997,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____2029 =
          let uu____2031 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____2031 "\""  in
        Prims.op_Hat "\"" uu____2029
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____2037 =
          let uu____2039 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____2039 "\""  in
        Prims.op_Hat "\"" uu____2037
    | uu____2043 ->
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
              let uu____2102 =
                let uu____2103 = combine (text " * ") doc1  in
                hbox uu____2103  in
              parens uu____2102  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____2113 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____2119 =
                    let uu____2120 = combine (text ", ") args1  in
                    hbox uu____2120  in
                  parens uu____2119
               in
            let name1 = ptsym currentModule name  in
            let uu____2124 = reduce1 [args1; text name1]  in hbox uu____2124
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2126,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____2130 =
              let uu____2131 = reduce1 [d1; text " -> "; d2]  in
              hbox uu____2131  in
            maybe_paren outer t_prio_fun uu____2130
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____2133 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2133 then text "obj" else text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____2145 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____2145

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
            let uu____2238 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2238
            then
              let uu____2241 = reduce [text "Prims.unsafe_coerce "; doc1]  in
              parens uu____2241
            else
              (let uu____2245 = reduce [text "Obj.magic "; parens doc1]  in
               parens uu____2245)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map (fun d  -> reduce [d; text ";"; hardline]) docs
               in
            let uu____2259 = reduce docs1  in parens uu____2259
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2261 = string_of_mlconstant c  in text uu____2261
        | FStar_Extraction_ML_Syntax.MLE_Var x -> text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2266 = ptsym currentModule path  in text uu____2266
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2300 =
              match uu____2300 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2311 =
                    let uu____2314 =
                      let uu____2315 = ptsym currentModule (path, name)  in
                      text uu____2315  in
                    [uu____2314; text "="; doc1]  in
                  reduce1 uu____2311
               in
            let uu____2322 =
              let uu____2323 = FStar_List.map for1 fields  in
              combine (text "; ") uu____2323  in
            cbrackets uu____2322
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2337 = is_standard_constructor ctor  in
              if uu____2337
              then
                let uu____2341 =
                  let uu____2348 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2348  in
                FStar_Pervasives_Native.snd uu____2341
              else ptctor currentModule ctor  in
            text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2375 = is_standard_constructor ctor  in
              if uu____2375
              then
                let uu____2379 =
                  let uu____2386 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2386  in
                FStar_Pervasives_Native.snd uu____2379
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) -> reduce [parens x; text "::"; xs]
              | (uu____2419,uu____2420) ->
                  let uu____2427 =
                    let uu____2430 =
                      let uu____2433 =
                        let uu____2434 = combine (text ", ") args1  in
                        parens uu____2434  in
                      [uu____2433]  in
                    (text name) :: uu____2430  in
                  reduce1 uu____2427
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2445 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   parens uu____2445) es
               in
            let docs1 =
              let uu____2447 = combine (text ", ") docs  in parens uu____2447
               in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2464 =
                  let uu____2467 =
                    let uu____2470 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2470]  in
                  hardline :: uu____2467  in
                reduce uu____2464
              else empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2479 =
              let uu____2480 =
                let uu____2483 =
                  let uu____2486 =
                    let uu____2489 = reduce1 [text "in"; body1]  in
                    [uu____2489]  in
                  doc1 :: uu____2486  in
                pre :: uu____2483  in
              combine hardline uu____2480  in
            parens uu____2479
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2500::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2502;
                    FStar_Extraction_ML_Syntax.loc = uu____2503;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2505)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2507;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2508;_}::[])
                 when
                 let uu____2552 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2552 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2578;
                            FStar_Extraction_ML_Syntax.loc = uu____2579;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2581;
                       FStar_Extraction_ML_Syntax.loc = uu____2582;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2640;
                   FStar_Extraction_ML_Syntax.loc = uu____2641;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2654;
                   FStar_Extraction_ML_Syntax.loc = uu____2655;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2662 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2673 = reduce1 (e2 :: args1)  in parens uu____2673)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____2678 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2678
              then
                reduce [e2; text "."; text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2688 =
                   let uu____2691 =
                     let uu____2694 =
                       let uu____2697 =
                         let uu____2698 = ptsym currentModule f  in
                         text uu____2698  in
                       [uu____2697]  in
                     (text ".") :: uu____2694  in
                   e2 :: uu____2691  in
                 reduce uu____2688)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2734 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2734
              then
                let uu____2737 =
                  let uu____2740 =
                    let uu____2743 =
                      let uu____2746 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2748 =
                              let uu____2751 =
                                let uu____2754 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2754]  in
                              (text " : ") :: uu____2751  in
                            reduce1 uu____2748
                        | uu____2756 -> text ""  in
                      [uu____2746; text ")"]  in
                    (text x) :: uu____2743  in
                  (text "(") :: uu____2740  in
                reduce1 uu____2737
              else text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2775  ->
                   match uu____2775 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____2787 =
                let uu____2790 =
                  let uu____2793 = reduce1 ids1  in
                  [uu____2793; text "->"; body1]  in
                (text "fun") :: uu____2790  in
              reduce1 uu____2787  in
            parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2802 =
                let uu____2805 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2809 =
                  let uu____2812 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2812; text "end"]  in
                uu____2805 :: uu____2809  in
              combine hardline uu____2802  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2821 =
                let uu____2824 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2828 =
                  let uu____2831 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2832 =
                    let uu____2835 =
                      reduce1 [text "end"; text "else"; text "begin"]  in
                    let uu____2839 =
                      let uu____2842 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2842; text "end"]  in
                    uu____2835 :: uu____2839  in
                  uu____2831 :: uu____2832  in
                uu____2824 :: uu____2828  in
              combine hardline uu____2821  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2881 =
                reduce1 [text "match"; parens cond1; text "with"]  in
              uu____2881 :: pats1  in
            let doc2 = combine hardline doc1  in parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2888 =
              let uu____2891 =
                let uu____2894 =
                  let uu____2895 = ptctor currentModule exn  in
                  text uu____2895  in
                [uu____2894]  in
              (text "raise") :: uu____2891  in
            reduce1 uu____2888
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2907 =
              let uu____2910 =
                let uu____2913 =
                  let uu____2914 = ptctor currentModule exn  in
                  text uu____2914  in
                let uu____2916 =
                  let uu____2919 =
                    let uu____2920 = combine (text ", ") args1  in
                    parens uu____2920  in
                  [uu____2919]  in
                uu____2913 :: uu____2916  in
              (text "raise") :: uu____2910  in
            reduce1 uu____2907
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2945 =
              let uu____2948 =
                let uu____2951 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2952 =
                  let uu____2955 =
                    let uu____2958 =
                      let uu____2959 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      combine hardline uu____2959  in
                    [uu____2958]  in
                  (text "with") :: uu____2955  in
                uu____2951 :: uu____2952  in
              (text "try") :: uu____2948  in
            combine hardline uu____2945
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
          let uu____2983 =
            let uu____2997 = as_bin_op p  in FStar_Option.get uu____2997  in
          match uu____2983 with
          | (uu____3026,prio,txt) ->
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
        let uu____3050 =
          let uu____3057 = as_uni_op p  in FStar_Option.get uu____3057  in
        match uu____3050 with
        | (uu____3072,txt) ->
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
          let uu____3085 = string_of_mlconstant c  in text uu____3085
      | FStar_Extraction_ML_Syntax.MLP_Var x -> text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____3121 =
            match uu____3121 with
            | (name,p) ->
                let uu____3131 =
                  let uu____3134 =
                    let uu____3135 = ptsym currentModule (path, name)  in
                    text uu____3135  in
                  let uu____3141 =
                    let uu____3144 =
                      let uu____3147 = doc_of_pattern currentModule p  in
                      [uu____3147]  in
                    (text "=") :: uu____3144  in
                  uu____3134 :: uu____3141  in
                reduce1 uu____3131
             in
          let uu____3149 =
            let uu____3150 = FStar_List.map for1 fields  in
            combine (text "; ") uu____3150  in
          cbrackets uu____3149
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____3164 = is_standard_constructor ctor  in
            if uu____3164
            then
              let uu____3168 =
                let uu____3175 = as_standard_constructor ctor  in
                FStar_Option.get uu____3175  in
              FStar_Pervasives_Native.snd uu____3168
            else ptctor currentModule ctor  in
          text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3202 = is_standard_constructor ctor  in
            if uu____3202
            then
              let uu____3206 =
                let uu____3213 = as_standard_constructor ctor  in
                FStar_Option.get uu____3213  in
              FStar_Pervasives_Native.snd uu____3206
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3242 =
                  let uu____3245 =
                    let uu____3246 = doc_of_pattern currentModule x  in
                    parens uu____3246  in
                  let uu____3247 =
                    let uu____3250 =
                      let uu____3253 = doc_of_pattern currentModule xs  in
                      [uu____3253]  in
                    (text "::") :: uu____3250  in
                  uu____3245 :: uu____3247  in
                reduce uu____3242
            | (uu____3255,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3256)::[]) ->
                let uu____3263 =
                  let uu____3266 =
                    let uu____3269 =
                      let uu____3270 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3270  in
                    [uu____3269]  in
                  (text name) :: uu____3266  in
                reduce1 uu____3263
            | uu____3271 ->
                let uu____3279 =
                  let uu____3282 =
                    let uu____3285 =
                      let uu____3286 =
                        let uu____3287 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        combine (text ", ") uu____3287  in
                      parens uu____3286  in
                    [uu____3285]  in
                  (text name) :: uu____3282  in
                reduce1 uu____3279
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3302 = combine (text ", ") ps1  in parens uu____3302
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map parens ps1  in combine (text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> doc)
  =
  fun currentModule  ->
    fun uu____3315  ->
      match uu____3315 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3325 =
                  let uu____3328 =
                    let uu____3331 = doc_of_pattern currentModule p  in
                    [uu____3331]  in
                  (text "|") :: uu____3328  in
                reduce1 uu____3325
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3335 =
                  let uu____3338 =
                    let uu____3341 = doc_of_pattern currentModule p  in
                    [uu____3341; text "when"; c1]  in
                  (text "|") :: uu____3338  in
                reduce1 uu____3335
             in
          let uu____3344 =
            let uu____3347 = reduce1 [case; text "->"; text "begin"]  in
            let uu____3350 =
              let uu____3353 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3353; text "end"]  in
            uu____3347 :: uu____3350  in
          combine hardline uu____3344

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> doc)
  =
  fun currentModule  ->
    fun uu____3356  ->
      match uu____3356 with
      | (rec_,top_level,lets) ->
          let for1 uu____3381 =
            match uu____3381 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3384;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3386;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then text ""
                  else
                    (let uu____3402 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3402
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3405::uu____3406,uu____3407) -> text ""
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
                                let uu____3431 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3431 reduce1  in
                              reduce1 [text ":"; vars; text "."; ty1])
                       else text "")
                   in
                let uu____3450 =
                  let uu____3453 =
                    let uu____3456 = reduce1 ids  in
                    [uu____3456; ty_annot; text "="; e1]  in
                  (text name) :: uu____3453  in
                reduce1 uu____3450
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
  fun uu____3482  ->
    match uu____3482 with
    | (lineno,file) ->
        let uu____3489 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3489
        then empty
        else
          (let file1 = FStar_Util.basename file  in
           let uu____3498 =
             let uu____3501 =
               let uu____3504 = num lineno  in
               [uu____3504;
               text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))]  in
             (text "#") :: uu____3501  in
           reduce1 uu____3498)

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____3548 =
        match uu____3548 with
        | (uu____3571,x,mangle_opt,tparams,uu____3575,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> empty
              | x2::[] -> text x2
              | uu____3610 ->
                  let doc1 = FStar_List.map (fun x2  -> text x2) tparams  in
                  let uu____3621 = combine (text ", ") doc1  in
                  parens uu____3621
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3648 =
                    match uu____3648 with
                    | (name,ty) ->
                        let name1 = text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        reduce1 [name1; text ":"; ty1]
                     in
                  let uu____3661 =
                    let uu____3662 = FStar_List.map forfield fields  in
                    combine (text "; ") uu____3662  in
                  cbrackets uu____3661
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3703 =
                    match uu____3703 with
                    | (name,tys) ->
                        let uu____3734 = FStar_List.split tys  in
                        (match uu____3734 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> text name
                              | uu____3757 ->
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
              let uu____3788 =
                let uu____3791 =
                  let uu____3794 =
                    let uu____3795 = ptsym currentModule ([], x1)  in
                    text uu____3795  in
                  [uu____3794]  in
                tparams1 :: uu____3791  in
              reduce1 uu____3788  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3804 =
                   let uu____3807 = reduce1 [doc1; text "="]  in
                   [uu____3807; body2]  in
                 combine hardline uu____3804)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > Prims.int_zero
        then
          let uu____3815 =
            let uu____3818 =
              let uu____3821 = combine (text " \n and ") doc1  in
              [uu____3821]  in
            (text "type") :: uu____3818  in
          reduce1 uu____3815
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
          let uu____3857 =
            let uu____3860 = reduce1 [text "module"; text x; text "="]  in
            let uu____3863 =
              let uu____3866 = doc_of_sig currentModule subsig  in
              let uu____3867 =
                let uu____3870 = reduce1 [text "end"]  in [uu____3870]  in
              uu____3866 :: uu____3867  in
            uu____3860 :: uu____3863  in
          combine hardline uu____3857
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3890 = combine (text " * ") args1  in parens uu____3890
             in
          reduce1 [text "exception"; text x; text "of"; args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3895,ty)) ->
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
            let uu____3974 = combine (text " * ") args2  in parens uu____3974
             in
          reduce1 [text "exception"; text x; text "of"; args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____3990 =
            let uu____3993 =
              let uu____3996 =
                let uu____3999 =
                  let uu____4002 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____4002]  in
                (text "=") :: uu____3999  in
              (text "_") :: uu____3996  in
            (text "let") :: uu____3993  in
          reduce1 uu____3990
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____4032 -> empty
              | uu____4033 -> hardline);
             hardline]) m
         in
      reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun uu____4046  ->
    match uu____4046 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____4116 =
          match uu____4116 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head1 =
                reduce1 [text "module"; text x1; text ":"; text "sig"]  in
              let tail1 = reduce1 [text "end"]  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4176  ->
                     match uu____4176 with
                     | (s,uu____4182) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map (fun x2  -> reduce [x2; hardline; hardline])
                  sub2
                 in
              let uu____4203 =
                let uu____4206 =
                  let uu____4209 =
                    let uu____4212 = reduce sub3  in
                    [uu____4212; cat tail1 hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> empty
                   | FStar_Pervasives_Native.Some s -> cat s hardline) ::
                    uu____4209
                   in
                (cat head1 hardline) :: uu____4206  in
              reduce uu____4203
        
        and for1_mod istop uu____4215 =
          match uu____4215 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4297 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [hardline; text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____4318 =
                  let uu____4321 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4321
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
                reduce1 uu____4318  in
              let tail1 =
                if Prims.op_Negation istop
                then reduce1 [text "end"]
                else reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4352  ->
                     match uu____4352 with
                     | (uu____4357,m) -> doc_of_mod target_mod_name m) sigmod
                 in
              let sub2 = FStar_List.map (for1_mod false) sub1  in
              let sub3 =
                FStar_List.map (fun x  -> reduce [x; hardline; hardline])
                  sub2
                 in
              let prefix1 =
                let uu____4383 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4383
                then [cat (text "#light \"off\"") hardline]
                else []  in
              let uu____4391 =
                let uu____4394 =
                  let uu____4397 =
                    let uu____4400 =
                      let uu____4403 =
                        let uu____4406 =
                          let uu____4409 = reduce sub3  in
                          [uu____4409; cat tail1 hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  -> empty
                         | FStar_Pervasives_Native.Some s -> cat s hardline)
                          :: uu____4406
                         in
                      hardline :: uu____4403  in
                    FStar_List.append maybe_open_pervasives uu____4400  in
                  FStar_List.append [head1; hardline; text "open Prims"]
                    uu____4397
                   in
                FStar_List.append prefix1 uu____4394  in
              FStar_All.pipe_left reduce uu____4391
         in
        let docs =
          FStar_List.map
            (fun uu____4453  ->
               match uu____4453 with
               | (x,s,m) ->
                   let uu____4510 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4512 = for1_mod true (x, s, m)  in
                   (uu____4510, uu____4512)) mllib
           in
        docs
  
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____4541  -> match uu____4541 with | Doc doc1 -> doc1 
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
        let uu____4572 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4572 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____4588 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4588 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc1
  