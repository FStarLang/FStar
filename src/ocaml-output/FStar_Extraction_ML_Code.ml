open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____58018 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____58029 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____58040 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____58051 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____58062 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____58078 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____58089 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____58101 -> false
  
let (__proj__Infix__item___0 : fixity -> assoc) =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int * fixity)
type level = (opprec * assoc)
let (t_prio_fun : (Prims.int * fixity)) =
  ((Prims.parse_int "10"), (Infix Right)) 
let (t_prio_tpl : (Prims.int * fixity)) =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let (t_prio_name : (Prims.int * fixity)) = ((Prims.parse_int "30"), Postfix) 
let (e_bin_prio_lambda : (Prims.int * fixity)) =
  ((Prims.parse_int "5"), Prefix) 
let (e_bin_prio_if : (Prims.int * fixity)) = ((Prims.parse_int "15"), Prefix) 
let (e_bin_prio_letin : (Prims.int * fixity)) =
  ((Prims.parse_int "19"), Prefix) 
let (e_bin_prio_or : (Prims.int * fixity)) =
  ((Prims.parse_int "20"), (Infix Left)) 
let (e_bin_prio_and : (Prims.int * fixity)) =
  ((Prims.parse_int "25"), (Infix Left)) 
let (e_bin_prio_eq : (Prims.int * fixity)) =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let (e_bin_prio_order : (Prims.int * fixity)) =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let (e_bin_prio_op1 : (Prims.int * fixity)) =
  ((Prims.parse_int "30"), (Infix Left)) 
let (e_bin_prio_op2 : (Prims.int * fixity)) =
  ((Prims.parse_int "40"), (Infix Left)) 
let (e_bin_prio_op3 : (Prims.int * fixity)) =
  ((Prims.parse_int "50"), (Infix Left)) 
let (e_bin_prio_op4 : (Prims.int * fixity)) =
  ((Prims.parse_int "60"), (Infix Left)) 
let (e_bin_prio_comb : (Prims.int * fixity)) =
  ((Prims.parse_int "70"), (Infix Left)) 
let (e_bin_prio_seq : (Prims.int * fixity)) =
  ((Prims.parse_int "100"), (Infix Left)) 
let (e_app_prio : (Prims.int * fixity)) =
  ((Prims.parse_int "10000"), (Infix Left)) 
let (min_op_prec : (Prims.int * fixity)) =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let (max_op_prec : (Prims.int * fixity)) =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns : 'a . ('a Prims.list * 'a Prims.list) -> Prims.bool =
  fun x  ->
    match x with
    | ([],uu____58298) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____58322,uu____58323) -> false
  
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
                  let uu____58404 = FStar_Util.first_N cg_len ns  in
                  match uu____58404 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____58444 =
                           let uu____58448 =
                             let uu____58452 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____58452]  in
                           FStar_List.append pfx uu____58448  in
                         FStar_Pervasives_Native.Some uu____58444
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
      let uu____58498 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____58498 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____58514 ->
          let uu____58516 = x  in
          (match uu____58516 with
           | (ns,x1) ->
               let uu____58527 = path_of_ns currentModule ns  in
               (uu____58527, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____58545 =
      let uu____58547 =
        let uu____58549 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____58549  in
      let uu____58552 = FStar_String.get s (Prims.parse_int "0")  in
      uu____58547 <> uu____58552  in
    if uu____58545 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____58588 = mlpath_of_mlpath currentModule mlp  in
         match uu____58588 with
         | (p,s) ->
             let uu____58600 =
               let uu____58604 =
                 let uu____58608 = ptsym_of_symbol s  in [uu____58608]  in
               FStar_List.append p uu____58604  in
             FStar_String.concat "." uu____58600)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____58629 = mlpath_of_mlpath currentModule mlp  in
      match uu____58629 with
      | (p,s) ->
          let s1 =
            let uu____58643 =
              let uu____58645 =
                let uu____58647 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____58647  in
              let uu____58650 = FStar_String.get s (Prims.parse_int "0")  in
              uu____58645 <> uu____58650  in
            if uu____58643 then Prims.op_Hat "U__" s else s  in
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
  fun uu____59013  ->
    let op_minus =
      let uu____59016 =
        let uu____59018 = FStar_Options.codegen ()  in
        uu____59018 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____59016 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____59067 . unit -> 'Auu____59067 Prims.list =
  fun uu____59070  -> [] 
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
  fun uu____59165  ->
    match uu____59165 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59224  ->
               match uu____59224 with | (y,uu____59240,uu____59241) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59279 = as_bin_op p  in
    uu____59279 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59336  ->
    match uu____59336 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____59364 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____59382  ->
               match uu____59382 with | (y,uu____59391) -> x = y) uu____59364
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59412 = as_uni_op p  in
    uu____59412 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59456  ->
    match uu____59456 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59493  ->
               match uu____59493 with | (y,uu____59502) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59523 = as_standard_constructor p  in
    uu____59523 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____59573  ->
    fun inner  ->
      fun doc1  ->
        match uu____59573 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____59639 = _inner  in
              match uu____59639 with
              | (pi,fi) ->
                  let uu____59650 = _outer  in
                  (match uu____59650 with
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
                           | (uu____59668,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____59670,uu____59671) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___543_59710  ->
      if uu___543_59710 = 92
      then "\\\\"
      else
        if uu___543_59710 = 32
        then " "
        else
          if uu___543_59710 = 8
          then "\\b"
          else
            if uu___543_59710 = 9
            then "\\t"
            else
              if uu___543_59710 = 13
              then "\\r"
              else
                if uu___543_59710 = 10
                then "\\n"
                else
                  if uu___543_59710 = 39
                  then "\\'"
                  else
                    if uu___543_59710 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_59710
                      then FStar_Util.string_of_char uu___543_59710
                      else
                        if FStar_Util.is_punctuation uu___543_59710
                        then FStar_Util.string_of_char uu___543_59710
                        else
                          if FStar_Util.is_symbol uu___543_59710
                          then FStar_Util.string_of_char uu___543_59710
                          else fallback uu___543_59710
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____59757 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____59757
          (if
             ((nc >= (Prims.parse_int "32")) &&
                (nc <= (Prims.parse_int "127")))
               && (nc <> (Prims.parse_int "34"))
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
        (s,FStar_Pervasives_Native.Some (uu____59799,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____59813,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____59845 =
          let uu____59847 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____59847 "\""  in
        Prims.op_Hat "\"" uu____59845
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____59853 =
          let uu____59855 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____59855 "\""  in
        Prims.op_Hat "\"" uu____59853
    | uu____59859 ->
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
              let uu____59918 =
                let uu____59919 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____59919  in
              FStar_Format.parens uu____59918  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____59929 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____59935 =
                    let uu____59936 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____59936  in
                  FStar_Format.parens uu____59935
               in
            let name1 = ptsym currentModule name  in
            let uu____59940 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____59940
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____59942,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____59946 =
              let uu____59947 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____59947  in
            maybe_paren outer t_prio_fun uu____59946
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____59949 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____59949
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> FStar_Format.text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____59961 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____59961

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
            let uu____60054 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60054
            then
              let uu____60057 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____60057
            else
              (let uu____60061 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____60061)
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
            let uu____60075 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____60075
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____60077 = string_of_mlconstant c  in
            FStar_Format.text uu____60077
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____60082 = ptsym currentModule path  in
            FStar_Format.text uu____60082
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____60116 =
              match uu____60116 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60127 =
                    let uu____60130 =
                      let uu____60131 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____60131  in
                    [uu____60130; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____60127
               in
            let uu____60138 =
              let uu____60139 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____60139  in
            FStar_Format.cbrackets uu____60138
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____60153 = is_standard_constructor ctor  in
              if uu____60153
              then
                let uu____60157 =
                  let uu____60164 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60164  in
                FStar_Pervasives_Native.snd uu____60157
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____60191 = is_standard_constructor ctor  in
              if uu____60191
              then
                let uu____60195 =
                  let uu____60202 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60202  in
                FStar_Pervasives_Native.snd uu____60195
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
              | (uu____60235,uu____60236) ->
                  let uu____60243 =
                    let uu____60246 =
                      let uu____60249 =
                        let uu____60250 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____60250  in
                      [uu____60249]  in
                    (FStar_Format.text name) :: uu____60246  in
                  FStar_Format.reduce1 uu____60243
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____60261 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____60261) es
               in
            let docs1 =
              let uu____60263 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____60263  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____60280 =
                  let uu____60283 =
                    let uu____60286 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____60286]  in
                  FStar_Format.hardline :: uu____60283  in
                FStar_Format.reduce uu____60280
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____60295 =
              let uu____60296 =
                let uu____60299 =
                  let uu____60302 =
                    let uu____60305 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____60305]  in
                  doc1 :: uu____60302  in
                pre :: uu____60299  in
              FStar_Format.combine FStar_Format.hardline uu____60296  in
            FStar_Format.parens uu____60295
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____60316::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____60318;
                    FStar_Extraction_ML_Syntax.loc = uu____60319;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____60321)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____60323;
                  FStar_Extraction_ML_Syntax.loc = uu____60324;_}::[])
                 when
                 let uu____60368 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____60368 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____60394;
                            FStar_Extraction_ML_Syntax.loc = uu____60395;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____60397;
                       FStar_Extraction_ML_Syntax.loc = uu____60398;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60456;
                   FStar_Extraction_ML_Syntax.loc = uu____60457;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60470;
                   FStar_Extraction_ML_Syntax.loc = uu____60471;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____60478 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____60489 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____60489)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____60494 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60494
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____60504 =
                   let uu____60507 =
                     let uu____60510 =
                       let uu____60513 =
                         let uu____60514 = ptsym currentModule f  in
                         FStar_Format.text uu____60514  in
                       [uu____60513]  in
                     (FStar_Format.text ".") :: uu____60510  in
                   e2 :: uu____60507  in
                 FStar_Format.reduce uu____60504)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____60550 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60550
              then
                let uu____60553 =
                  let uu____60556 =
                    let uu____60559 =
                      let uu____60562 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____60564 =
                              let uu____60567 =
                                let uu____60570 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____60570]  in
                              (FStar_Format.text " : ") :: uu____60567  in
                            FStar_Format.reduce1 uu____60564
                        | uu____60572 -> FStar_Format.text ""  in
                      [uu____60562; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____60559  in
                  (FStar_Format.text "(") :: uu____60556  in
                FStar_Format.reduce1 uu____60553
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____60591  ->
                   match uu____60591 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____60603 =
                let uu____60606 =
                  let uu____60609 = FStar_Format.reduce1 ids1  in
                  [uu____60609; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____60606  in
              FStar_Format.reduce1 uu____60603  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60618 =
                let uu____60621 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60625 =
                  let uu____60628 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____60628; FStar_Format.text "end"]  in
                uu____60621 :: uu____60625  in
              FStar_Format.combine FStar_Format.hardline uu____60618  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60637 =
                let uu____60640 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60644 =
                  let uu____60647 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60648 =
                    let uu____60651 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____60655 =
                      let uu____60658 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____60658; FStar_Format.text "end"]  in
                    uu____60651 :: uu____60655  in
                  uu____60647 :: uu____60648  in
                uu____60640 :: uu____60644  in
              FStar_Format.combine FStar_Format.hardline uu____60637  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____60697 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____60697 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____60704 =
              let uu____60707 =
                let uu____60710 =
                  let uu____60711 = ptctor currentModule exn  in
                  FStar_Format.text uu____60711  in
                [uu____60710]  in
              (FStar_Format.text "raise") :: uu____60707  in
            FStar_Format.reduce1 uu____60704
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____60723 =
              let uu____60726 =
                let uu____60729 =
                  let uu____60730 = ptctor currentModule exn  in
                  FStar_Format.text uu____60730  in
                let uu____60732 =
                  let uu____60735 =
                    let uu____60736 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____60736  in
                  [uu____60735]  in
                uu____60729 :: uu____60732  in
              (FStar_Format.text "raise") :: uu____60726  in
            FStar_Format.reduce1 uu____60723
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____60761 =
              let uu____60764 =
                let uu____60767 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____60768 =
                  let uu____60771 =
                    let uu____60774 =
                      let uu____60775 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____60775
                       in
                    [uu____60774]  in
                  (FStar_Format.text "with") :: uu____60771  in
                uu____60767 :: uu____60768  in
              (FStar_Format.text "try") :: uu____60764  in
            FStar_Format.combine FStar_Format.hardline uu____60761
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
          let uu____60799 =
            let uu____60813 = as_bin_op p  in FStar_Option.get uu____60813
             in
          match uu____60799 with
          | (uu____60842,prio,txt) ->
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
        let uu____60866 =
          let uu____60873 = as_uni_op p  in FStar_Option.get uu____60873  in
        match uu____60866 with
        | (uu____60888,txt) ->
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
          let uu____60901 = string_of_mlconstant c  in
          FStar_Format.text uu____60901
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____60937 =
            match uu____60937 with
            | (name,p) ->
                let uu____60947 =
                  let uu____60950 =
                    let uu____60951 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____60951  in
                  let uu____60957 =
                    let uu____60960 =
                      let uu____60963 = doc_of_pattern currentModule p  in
                      [uu____60963]  in
                    (FStar_Format.text "=") :: uu____60960  in
                  uu____60950 :: uu____60957  in
                FStar_Format.reduce1 uu____60947
             in
          let uu____60965 =
            let uu____60966 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____60966  in
          FStar_Format.cbrackets uu____60965
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____60980 = is_standard_constructor ctor  in
            if uu____60980
            then
              let uu____60984 =
                let uu____60991 = as_standard_constructor ctor  in
                FStar_Option.get uu____60991  in
              FStar_Pervasives_Native.snd uu____60984
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____61018 = is_standard_constructor ctor  in
            if uu____61018
            then
              let uu____61022 =
                let uu____61029 = as_standard_constructor ctor  in
                FStar_Option.get uu____61029  in
              FStar_Pervasives_Native.snd uu____61022
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____61058 =
                  let uu____61061 =
                    let uu____61062 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____61062  in
                  let uu____61063 =
                    let uu____61066 =
                      let uu____61069 = doc_of_pattern currentModule xs  in
                      [uu____61069]  in
                    (FStar_Format.text "::") :: uu____61066  in
                  uu____61061 :: uu____61063  in
                FStar_Format.reduce uu____61058
            | (uu____61071,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____61072)::[]) ->
                let uu____61079 =
                  let uu____61082 =
                    let uu____61085 =
                      let uu____61086 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____61086  in
                    [uu____61085]  in
                  (FStar_Format.text name) :: uu____61082  in
                FStar_Format.reduce1 uu____61079
            | uu____61087 ->
                let uu____61095 =
                  let uu____61098 =
                    let uu____61101 =
                      let uu____61102 =
                        let uu____61103 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____61103
                         in
                      FStar_Format.parens uu____61102  in
                    [uu____61101]  in
                  (FStar_Format.text name) :: uu____61098  in
                FStar_Format.reduce1 uu____61095
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____61118 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____61118
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61131  ->
      match uu____61131 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____61141 =
                  let uu____61144 =
                    let uu____61147 = doc_of_pattern currentModule p  in
                    [uu____61147]  in
                  (FStar_Format.text "|") :: uu____61144  in
                FStar_Format.reduce1 uu____61141
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____61151 =
                  let uu____61154 =
                    let uu____61157 = doc_of_pattern currentModule p  in
                    [uu____61157; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____61154  in
                FStar_Format.reduce1 uu____61151
             in
          let uu____61160 =
            let uu____61163 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____61166 =
              let uu____61169 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____61169; FStar_Format.text "end"]  in
            uu____61163 :: uu____61166  in
          FStar_Format.combine FStar_Format.hardline uu____61160

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61172  ->
      match uu____61172 with
      | (rec_,top_level,lets) ->
          let for1 uu____61197 =
            match uu____61197 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____61200;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____61202;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____61218 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____61218
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____61221::uu____61222,uu____61223) ->
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
                                let uu____61247 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____61247
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____61266 =
                  let uu____61269 =
                    let uu____61272 = FStar_Format.reduce1 ids  in
                    [uu____61272; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____61269  in
                FStar_Format.reduce1 uu____61266
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
  fun uu____61298  ->
    match uu____61298 with
    | (lineno,file) ->
        let uu____61305 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____61305
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))])

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____61357 =
        match uu____61357 with
        | (uu____61380,x,mangle_opt,tparams,uu____61384,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____61419 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____61430 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____61430
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____61457 =
                    match uu____61457 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____61470 =
                    let uu____61471 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____61471
                     in
                  FStar_Format.cbrackets uu____61470
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____61512 =
                    match uu____61512 with
                    | (name,tys) ->
                        let uu____61543 = FStar_List.split tys  in
                        (match uu____61543 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____61566 ->
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
              let uu____61597 =
                let uu____61600 =
                  let uu____61603 =
                    let uu____61604 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____61604  in
                  [uu____61603]  in
                tparams1 :: uu____61600  in
              FStar_Format.reduce1 uu____61597  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____61613 =
                   let uu____61616 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____61616; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____61613)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____61624 =
            let uu____61627 =
              let uu____61630 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____61630]  in
            (FStar_Format.text "type") :: uu____61627  in
          FStar_Format.reduce1 uu____61624
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
          let uu____61666 =
            let uu____61669 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____61672 =
              let uu____61675 = doc_of_sig currentModule subsig  in
              let uu____61676 =
                let uu____61679 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____61679]  in
              uu____61675 :: uu____61676  in
            uu____61669 :: uu____61672  in
          FStar_Format.combine FStar_Format.hardline uu____61666
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____61699 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____61699  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____61704,ty)) ->
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
            let uu____61783 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____61783  in
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
          let uu____61799 =
            let uu____61802 =
              let uu____61805 =
                let uu____61808 =
                  let uu____61811 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____61811]  in
                (FStar_Format.text "=") :: uu____61808  in
              (FStar_Format.text "_") :: uu____61805  in
            (FStar_Format.text "let") :: uu____61802  in
          FStar_Format.reduce1 uu____61799
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____61841 ->
                  FStar_Format.empty
              | uu____61842 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____61855  ->
    match uu____61855 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____61925 =
          match uu____61925 with
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
                  (fun uu____61985  ->
                     match uu____61985 with
                     | (s,uu____61991) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____62012 =
                let uu____62015 =
                  let uu____62018 =
                    let uu____62021 = FStar_Format.reduce sub3  in
                    [uu____62021;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____62018
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____62015
                 in
              FStar_Format.reduce uu____62012
        
        and for1_mod istop uu____62024 =
          match uu____62024 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____62106 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____62127 =
                  let uu____62130 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____62130
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
                FStar_Format.reduce1 uu____62127  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____62161  ->
                     match uu____62161 with
                     | (uu____62166,m) -> doc_of_mod target_mod_name m)
                  sigmod
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
                let uu____62192 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____62192
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____62200 =
                let uu____62203 =
                  let uu____62206 =
                    let uu____62209 =
                      let uu____62212 =
                        let uu____62215 =
                          let uu____62218 = FStar_Format.reduce sub3  in
                          [uu____62218;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____62215
                         in
                      FStar_Format.hardline :: uu____62212  in
                    FStar_List.append maybe_open_pervasives uu____62209  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____62206
                   in
                FStar_List.append prefix1 uu____62203  in
              FStar_All.pipe_left FStar_Format.reduce uu____62200
         in
        let docs =
          FStar_List.map
            (fun uu____62262  ->
               match uu____62262 with
               | (x,s,m) ->
                   let uu____62319 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____62321 = for1_mod true (x, s, m)  in
                   (uu____62319, uu____62321)) mllib
           in
        docs
  
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  = fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____62364 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____62364 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____62380 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____62380 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  