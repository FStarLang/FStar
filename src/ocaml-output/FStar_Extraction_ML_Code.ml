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
  
let prim_types : 'uuuuuu1235 . unit -> 'uuuuuu1235 Prims.list =
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
      fun doc1  ->
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
    fun uu___0_1881  ->
      if uu___0_1881 = 92
      then "\\\\"
      else
        if uu___0_1881 = 32
        then " "
        else
          if uu___0_1881 = 8
          then "\\b"
          else
            if uu___0_1881 = 9
            then "\\t"
            else
              if uu___0_1881 = 13
              then "\\r"
              else
                if uu___0_1881 = 10
                then "\\n"
                else
                  if uu___0_1881 = 39
                  then "\\'"
                  else
                    if uu___0_1881 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___0_1881
                      then FStar_Util.string_of_char uu___0_1881
                      else
                        if FStar_Util.is_punctuation uu___0_1881
                        then FStar_Util.string_of_char uu___0_1881
                        else
                          if FStar_Util.is_symbol uu___0_1881
                          then FStar_Util.string_of_char uu___0_1881
                          else fallback uu___0_1881
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____1928 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____1928
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
        (s,FStar_Pervasives_Native.Some (uu____1970,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1984,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____2017 =
          let uu____2019 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____2019 "\""  in
        Prims.op_Hat "\"" uu____2017
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____2025 =
          let uu____2027 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____2027 "\""  in
        Prims.op_Hat "\"" uu____2025
    | uu____2031 ->
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
              let uu____2090 =
                let uu____2091 = combine (text " * ") doc1  in
                hbox uu____2091  in
              parens uu____2090  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____2101 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____2107 =
                    let uu____2108 = combine (text ", ") args1  in
                    hbox uu____2108  in
                  parens uu____2107
               in
            let name1 = ptsym currentModule name  in
            let uu____2112 = reduce1 [args1; text name1]  in hbox uu____2112
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2114,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____2118 =
              let uu____2119 = reduce1 [d1; text " -> "; d2]  in
              hbox uu____2119  in
            maybe_paren outer t_prio_fun uu____2118
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____2121 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2121 then text "obj" else text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____2133 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____2133

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
            let uu____2226 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____2226
            then
              let uu____2229 = reduce [text "Prims.unsafe_coerce "; doc1]  in
              parens uu____2229
            else
              (let uu____2233 = reduce [text "Obj.magic "; parens doc1]  in
               parens uu____2233)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map (fun d  -> reduce [d; text ";"; hardline]) docs
               in
            let uu____2247 = reduce docs1  in parens uu____2247
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____2249 = string_of_mlconstant c  in text uu____2249
        | FStar_Extraction_ML_Syntax.MLE_Var x -> text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____2254 = ptsym currentModule path  in text uu____2254
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____2288 =
              match uu____2288 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2299 =
                    let uu____2302 =
                      let uu____2303 = ptsym currentModule (path, name)  in
                      text uu____2303  in
                    [uu____2302; text "="; doc1]  in
                  reduce1 uu____2299
               in
            let uu____2310 =
              let uu____2311 = FStar_List.map for1 fields  in
              combine (text "; ") uu____2311  in
            cbrackets uu____2310
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____2325 = is_standard_constructor ctor  in
              if uu____2325
              then
                let uu____2329 =
                  let uu____2336 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2336  in
                FStar_Pervasives_Native.snd uu____2329
              else ptctor currentModule ctor  in
            text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____2363 = is_standard_constructor ctor  in
              if uu____2363
              then
                let uu____2367 =
                  let uu____2374 = as_standard_constructor ctor  in
                  FStar_Option.get uu____2374  in
                FStar_Pervasives_Native.snd uu____2367
              else ptctor currentModule ctor  in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) -> reduce [parens x; text "::"; xs]
              | (uu____2407,uu____2408) ->
                  let uu____2415 =
                    let uu____2418 =
                      let uu____2421 =
                        let uu____2422 = combine (text ", ") args1  in
                        parens uu____2422  in
                      [uu____2421]  in
                    (text name) :: uu____2418  in
                  reduce1 uu____2415
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____2433 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   parens uu____2433) es
               in
            let docs1 =
              let uu____2435 = combine (text ", ") docs  in parens uu____2435
               in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____2452 =
                  let uu____2455 =
                    let uu____2458 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____2458]  in
                  hardline :: uu____2455  in
                reduce uu____2452
              else empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____2467 =
              let uu____2468 =
                let uu____2471 =
                  let uu____2474 =
                    let uu____2477 = reduce1 [text "in"; body1]  in
                    [uu____2477]  in
                  doc1 :: uu____2474  in
                pre :: uu____2471  in
              combine hardline uu____2468  in
            parens uu____2467
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____2488::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____2490;
                    FStar_Extraction_ML_Syntax.loc = uu____2491;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____2493)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____2495;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____2496;_}::[])
                 when
                 let uu____2540 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____2540 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____2566;
                            FStar_Extraction_ML_Syntax.loc = uu____2567;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____2569;
                       FStar_Extraction_ML_Syntax.loc = uu____2570;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2628;
                   FStar_Extraction_ML_Syntax.loc = uu____2629;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____2642;
                   FStar_Extraction_ML_Syntax.loc = uu____2643;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____2650 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____2661 = reduce1 (e2 :: args1)  in parens uu____2661)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____2666 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2666
              then
                reduce [e2; text "."; text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____2676 =
                   let uu____2679 =
                     let uu____2682 =
                       let uu____2685 =
                         let uu____2686 = ptsym currentModule f  in
                         text uu____2686  in
                       [uu____2685]  in
                     (text ".") :: uu____2682  in
                   e2 :: uu____2679  in
                 reduce uu____2676)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____2722 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____2722
              then
                let uu____2725 =
                  let uu____2728 =
                    let uu____2731 =
                      let uu____2734 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____2736 =
                              let uu____2739 =
                                let uu____2742 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____2742]  in
                              (text " : ") :: uu____2739  in
                            reduce1 uu____2736
                        | uu____2744 -> text ""  in
                      [uu____2734; text ")"]  in
                    (text x) :: uu____2731  in
                  (text "(") :: uu____2728  in
                reduce1 uu____2725
              else text x  in
            let ids1 =
              FStar_List.map
                (fun uu____2763  ->
                   match uu____2763 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____2775 =
                let uu____2778 =
                  let uu____2781 = reduce1 ids1  in
                  [uu____2781; text "->"; body1]  in
                (text "fun") :: uu____2778  in
              reduce1 uu____2775  in
            parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2790 =
                let uu____2793 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2797 =
                  let uu____2800 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____2800; text "end"]  in
                uu____2793 :: uu____2797  in
              combine hardline uu____2790  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____2809 =
                let uu____2812 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"]  in
                let uu____2816 =
                  let uu____2819 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____2820 =
                    let uu____2823 =
                      reduce1 [text "end"; text "else"; text "begin"]  in
                    let uu____2827 =
                      let uu____2830 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____2830; text "end"]  in
                    uu____2823 :: uu____2827  in
                  uu____2819 :: uu____2820  in
                uu____2812 :: uu____2816  in
              combine hardline uu____2809  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____2869 =
                reduce1 [text "match"; parens cond1; text "with"]  in
              uu____2869 :: pats1  in
            let doc2 = combine hardline doc1  in parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____2876 =
              let uu____2879 =
                let uu____2882 =
                  let uu____2883 = ptctor currentModule exn  in
                  text uu____2883  in
                [uu____2882]  in
              (text "raise") :: uu____2879  in
            reduce1 uu____2876
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____2895 =
              let uu____2898 =
                let uu____2901 =
                  let uu____2902 = ptctor currentModule exn  in
                  text uu____2902  in
                let uu____2904 =
                  let uu____2907 =
                    let uu____2908 = combine (text ", ") args1  in
                    parens uu____2908  in
                  [uu____2907]  in
                uu____2901 :: uu____2904  in
              (text "raise") :: uu____2898  in
            reduce1 uu____2895
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____2933 =
              let uu____2936 =
                let uu____2939 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____2940 =
                  let uu____2943 =
                    let uu____2946 =
                      let uu____2947 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      combine hardline uu____2947  in
                    [uu____2946]  in
                  (text "with") :: uu____2943  in
                uu____2939 :: uu____2940  in
              (text "try") :: uu____2936  in
            combine hardline uu____2933
        | FStar_Extraction_ML_Syntax.MLE_TApp (head,ty_args) ->
            doc_of_expr currentModule outer head

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
          let uu____2971 =
            let uu____2985 = as_bin_op p  in FStar_Option.get uu____2985  in
          match uu____2971 with
          | (uu____3014,prio,txt) ->
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
        let uu____3038 =
          let uu____3045 = as_uni_op p  in FStar_Option.get uu____3045  in
        match uu____3038 with
        | (uu____3060,txt) ->
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
          let uu____3073 = string_of_mlconstant c  in text uu____3073
      | FStar_Extraction_ML_Syntax.MLP_Var x -> text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____3109 =
            match uu____3109 with
            | (name,p) ->
                let uu____3119 =
                  let uu____3122 =
                    let uu____3123 = ptsym currentModule (path, name)  in
                    text uu____3123  in
                  let uu____3129 =
                    let uu____3132 =
                      let uu____3135 = doc_of_pattern currentModule p  in
                      [uu____3135]  in
                    (text "=") :: uu____3132  in
                  uu____3122 :: uu____3129  in
                reduce1 uu____3119
             in
          let uu____3137 =
            let uu____3138 = FStar_List.map for1 fields  in
            combine (text "; ") uu____3138  in
          cbrackets uu____3137
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____3152 = is_standard_constructor ctor  in
            if uu____3152
            then
              let uu____3156 =
                let uu____3163 = as_standard_constructor ctor  in
                FStar_Option.get uu____3163  in
              FStar_Pervasives_Native.snd uu____3156
            else ptctor currentModule ctor  in
          text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____3190 = is_standard_constructor ctor  in
            if uu____3190
            then
              let uu____3194 =
                let uu____3201 = as_standard_constructor ctor  in
                FStar_Option.get uu____3201  in
              FStar_Pervasives_Native.snd uu____3194
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____3230 =
                  let uu____3233 =
                    let uu____3234 = doc_of_pattern currentModule x  in
                    parens uu____3234  in
                  let uu____3235 =
                    let uu____3238 =
                      let uu____3241 = doc_of_pattern currentModule xs  in
                      [uu____3241]  in
                    (text "::") :: uu____3238  in
                  uu____3233 :: uu____3235  in
                reduce uu____3230
            | (uu____3243,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____3244)::[]) ->
                let uu____3251 =
                  let uu____3254 =
                    let uu____3257 =
                      let uu____3258 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____3258  in
                    [uu____3257]  in
                  (text name) :: uu____3254  in
                reduce1 uu____3251
            | uu____3259 ->
                let uu____3267 =
                  let uu____3270 =
                    let uu____3273 =
                      let uu____3274 =
                        let uu____3275 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        combine (text ", ") uu____3275  in
                      parens uu____3274  in
                    [uu____3273]  in
                  (text name) :: uu____3270  in
                reduce1 uu____3267
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____3290 = combine (text ", ") ps1  in parens uu____3290
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map parens ps1  in combine (text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> doc)
  =
  fun currentModule  ->
    fun uu____3303  ->
      match uu____3303 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____3313 =
                  let uu____3316 =
                    let uu____3319 = doc_of_pattern currentModule p  in
                    [uu____3319]  in
                  (text "|") :: uu____3316  in
                reduce1 uu____3313
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____3323 =
                  let uu____3326 =
                    let uu____3329 = doc_of_pattern currentModule p  in
                    [uu____3329; text "when"; c1]  in
                  (text "|") :: uu____3326  in
                reduce1 uu____3323
             in
          let uu____3332 =
            let uu____3335 = reduce1 [case; text "->"; text "begin"]  in
            let uu____3338 =
              let uu____3341 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____3341; text "end"]  in
            uu____3335 :: uu____3338  in
          combine hardline uu____3332

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> doc)
  =
  fun currentModule  ->
    fun uu____3344  ->
      match uu____3344 with
      | (rec_,top_level,lets) ->
          let for1 uu____3369 =
            match uu____3369 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3372;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____3374;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then text ""
                  else
                    (let uu____3390 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____3390
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____3393::uu____3394,uu____3395) -> text ""
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
                                let uu____3419 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____3419 reduce1  in
                              reduce1 [text ":"; vars; text "."; ty1])
                       else text "")
                   in
                let uu____3438 =
                  let uu____3441 =
                    let uu____3444 = reduce1 ids  in
                    [uu____3444; ty_annot; text "="; e1]  in
                  (text name) :: uu____3441  in
                reduce1 uu____3438
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
  fun uu____3470  ->
    match uu____3470 with
    | (lineno,file) ->
        let uu____3477 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____3477
        then empty
        else
          (let file1 = FStar_Util.basename file  in
           let uu____3486 =
             let uu____3489 =
               let uu____3492 = num lineno  in
               [uu____3492;
               text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))]  in
             (text "#") :: uu____3489  in
           reduce1 uu____3486)

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____3536 =
        match uu____3536 with
        | (uu____3559,x,mangle_opt,tparams,uu____3563,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> empty
              | x2::[] -> text x2
              | uu____3598 ->
                  let doc1 = FStar_List.map (fun x2  -> text x2) tparams  in
                  let uu____3609 = combine (text ", ") doc1  in
                  parens uu____3609
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____3636 =
                    match uu____3636 with
                    | (name,ty) ->
                        let name1 = text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        reduce1 [name1; text ":"; ty1]
                     in
                  let uu____3649 =
                    let uu____3650 = FStar_List.map forfield fields  in
                    combine (text "; ") uu____3650  in
                  cbrackets uu____3649
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____3691 =
                    match uu____3691 with
                    | (name,tys) ->
                        let uu____3722 = FStar_List.split tys  in
                        (match uu____3722 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> text name
                              | uu____3745 ->
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
              let uu____3776 =
                let uu____3779 =
                  let uu____3782 =
                    let uu____3783 = ptsym currentModule ([], x1)  in
                    text uu____3783  in
                  [uu____3782]  in
                tparams1 :: uu____3779  in
              reduce1 uu____3776  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____3792 =
                   let uu____3795 = reduce1 [doc1; text "="]  in
                   [uu____3795; body2]  in
                 combine hardline uu____3792)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > Prims.int_zero
        then
          let uu____3803 =
            let uu____3806 =
              let uu____3809 = combine (text " \n and ") doc1  in
              [uu____3809]  in
            (text "type") :: uu____3806  in
          reduce1 uu____3803
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
          let uu____3845 =
            let uu____3848 = reduce1 [text "module"; text x; text "="]  in
            let uu____3851 =
              let uu____3854 = doc_of_sig currentModule subsig  in
              let uu____3855 =
                let uu____3858 = reduce1 [text "end"]  in [uu____3858]  in
              uu____3854 :: uu____3855  in
            uu____3848 :: uu____3851  in
          combine hardline uu____3845
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____3878 = combine (text " * ") args1  in parens uu____3878
             in
          reduce1 [text "exception"; text x; text "of"; args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____3883,ty)) ->
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
            let uu____3962 = combine (text " * ") args2  in parens uu____3962
             in
          reduce1 [text "exception"; text x; text "of"; args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____3978 =
            let uu____3981 =
              let uu____3984 =
                let uu____3987 =
                  let uu____3990 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____3990]  in
                (text "=") :: uu____3987  in
              (text "_") :: uu____3984  in
            (text "let") :: uu____3981  in
          reduce1 uu____3978
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____4020 -> empty
              | uu____4021 -> hardline);
             hardline]) m
         in
      reduce (FStar_List.flatten docs)
  
let (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun uu____4034  ->
    match uu____4034 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____4104 =
          match uu____4104 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head =
                reduce1 [text "module"; text x1; text ":"; text "sig"]  in
              let tail = reduce1 [text "end"]  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4164  ->
                     match uu____4164 with
                     | (s,uu____4170) -> doc_of_sig x1 s) sigmod
                 in
              let sub1 = FStar_List.map for1_sig sub  in
              let sub2 =
                FStar_List.map (fun x2  -> reduce [x2; hardline; hardline])
                  sub1
                 in
              let uu____4191 =
                let uu____4194 =
                  let uu____4197 =
                    let uu____4200 = reduce sub2  in
                    [uu____4200; cat tail hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> empty
                   | FStar_Pervasives_Native.Some s -> cat s hardline) ::
                    uu____4197
                   in
                (cat head hardline) :: uu____4194  in
              reduce uu____4191
        
        and for1_mod istop uu____4203 =
          match uu____4203 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name  in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____4285 ->
                    let pervasives =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [hardline; text (Prims.op_Hat "open " pervasives)]
                 in
              let head =
                let uu____4306 =
                  let uu____4309 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____4309
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
                reduce1 uu____4306  in
              let tail =
                if Prims.op_Negation istop
                then reduce1 [text "end"]
                else reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____4340  ->
                     match uu____4340 with
                     | (uu____4345,m) -> doc_of_mod target_mod_name m) sigmod
                 in
              let sub1 = FStar_List.map (for1_mod false) sub  in
              let sub2 =
                FStar_List.map (fun x  -> reduce [x; hardline; hardline])
                  sub1
                 in
              let prefix =
                let uu____4371 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____4371
                then [cat (text "#light \"off\"") hardline]
                else []  in
              let uu____4379 =
                let uu____4382 =
                  let uu____4385 =
                    let uu____4388 =
                      let uu____4391 =
                        let uu____4394 =
                          let uu____4397 = reduce sub2  in
                          [uu____4397; cat tail hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  -> empty
                         | FStar_Pervasives_Native.Some s -> cat s hardline)
                          :: uu____4394
                         in
                      hardline :: uu____4391  in
                    FStar_List.append maybe_open_pervasives uu____4388  in
                  FStar_List.append [head; hardline; text "open Prims"]
                    uu____4385
                   in
                FStar_List.append prefix uu____4382  in
              FStar_All.pipe_left reduce uu____4379
         in
        let docs =
          FStar_List.map
            (fun uu____4441  ->
               match uu____4441 with
               | (x,s,m) ->
                   let uu____4498 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____4500 = for1_mod true (x, s, m)  in
                   (uu____4498, uu____4500)) mllib
           in
        docs
  
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____4529  -> match uu____4529 with | Doc doc1 -> doc1 
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
        let uu____4560 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____4560 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____4576 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____4576 (min_op_prec, NonAssoc) e  in
      pretty Prims.int_zero doc1
  