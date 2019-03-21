open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____58019 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____58030 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____58041 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____58052 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____58063 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____58079 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____58090 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____58102 -> false
  
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
    | ([],uu____58299) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____58323,uu____58324) -> false
  
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
                  let uu____58405 = FStar_Util.first_N cg_len ns  in
                  match uu____58405 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____58445 =
                           let uu____58449 =
                             let uu____58453 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____58453]  in
                           FStar_List.append pfx uu____58449  in
                         FStar_Pervasives_Native.Some uu____58445
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
      let uu____58499 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____58499 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____58515 ->
          let uu____58517 = x  in
          (match uu____58517 with
           | (ns,x1) ->
               let uu____58528 = path_of_ns currentModule ns  in
               (uu____58528, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____58546 =
      let uu____58548 =
        let uu____58550 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____58550  in
      let uu____58553 = FStar_String.get s (Prims.parse_int "0")  in
      uu____58548 <> uu____58553  in
    if uu____58546 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____58589 = mlpath_of_mlpath currentModule mlp  in
         match uu____58589 with
         | (p,s) ->
             let uu____58601 =
               let uu____58605 =
                 let uu____58609 = ptsym_of_symbol s  in [uu____58609]  in
               FStar_List.append p uu____58605  in
             FStar_String.concat "." uu____58601)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____58630 = mlpath_of_mlpath currentModule mlp  in
      match uu____58630 with
      | (p,s) ->
          let s1 =
            let uu____58644 =
              let uu____58646 =
                let uu____58648 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____58648  in
              let uu____58651 = FStar_String.get s (Prims.parse_int "0")  in
              uu____58646 <> uu____58651  in
            if uu____58644 then Prims.op_Hat "U__" s else s  in
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
  fun uu____59014  ->
    let op_minus =
      let uu____59017 =
        let uu____59019 = FStar_Options.codegen ()  in
        uu____59019 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____59017 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____59068 . unit -> 'Auu____59068 Prims.list =
  fun uu____59071  -> [] 
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
  fun uu____59166  ->
    match uu____59166 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59225  ->
               match uu____59225 with | (y,uu____59241,uu____59242) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59280 = as_bin_op p  in
    uu____59280 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59337  ->
    match uu____59337 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____59365 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____59383  ->
               match uu____59383 with | (y,uu____59392) -> x = y) uu____59365
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59413 = as_uni_op p  in
    uu____59413 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59457  ->
    match uu____59457 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59494  ->
               match uu____59494 with | (y,uu____59503) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59524 = as_standard_constructor p  in
    uu____59524 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____59574  ->
    fun inner  ->
      fun doc1  ->
        match uu____59574 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____59640 = _inner  in
              match uu____59640 with
              | (pi,fi) ->
                  let uu____59651 = _outer  in
                  (match uu____59651 with
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
                           | (uu____59669,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____59671,uu____59672) -> false)))
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
    fun uu___543_59711  ->
      if uu___543_59711 = 92
      then "\\\\"
      else
        if uu___543_59711 = 32
        then " "
        else
          if uu___543_59711 = 8
          then "\\b"
          else
            if uu___543_59711 = 9
            then "\\t"
            else
              if uu___543_59711 = 13
              then "\\r"
              else
                if uu___543_59711 = 10
                then "\\n"
                else
                  if uu___543_59711 = 39
                  then "\\'"
                  else
                    if uu___543_59711 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_59711
                      then FStar_Util.string_of_char uu___543_59711
                      else
                        if FStar_Util.is_punctuation uu___543_59711
                        then FStar_Util.string_of_char uu___543_59711
                        else
                          if FStar_Util.is_symbol uu___543_59711
                          then FStar_Util.string_of_char uu___543_59711
                          else fallback uu___543_59711
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____59758 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____59758
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
        (s,FStar_Pervasives_Native.Some (uu____59800,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____59814,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____59846 =
          let uu____59848 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____59848 "\""  in
        Prims.op_Hat "\"" uu____59846
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____59854 =
          let uu____59856 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____59856 "\""  in
        Prims.op_Hat "\"" uu____59854
    | uu____59860 ->
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
              let uu____59919 =
                let uu____59920 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____59920  in
              FStar_Format.parens uu____59919  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____59930 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____59936 =
                    let uu____59937 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____59937  in
                  FStar_Format.parens uu____59936
               in
            let name1 = ptsym currentModule name  in
            let uu____59941 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____59941
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____59943,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____59947 =
              let uu____59948 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____59948  in
            maybe_paren outer t_prio_fun uu____59947
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____59950 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____59950
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
        let uu____59962 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____59962

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
            let uu____60055 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60055
            then
              let uu____60058 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____60058
            else
              (let uu____60062 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____60062)
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
            let uu____60076 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____60076
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____60078 = string_of_mlconstant c  in
            FStar_Format.text uu____60078
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____60083 = ptsym currentModule path  in
            FStar_Format.text uu____60083
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____60117 =
              match uu____60117 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60128 =
                    let uu____60131 =
                      let uu____60132 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____60132  in
                    [uu____60131; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____60128
               in
            let uu____60139 =
              let uu____60140 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____60140  in
            FStar_Format.cbrackets uu____60139
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____60154 = is_standard_constructor ctor  in
              if uu____60154
              then
                let uu____60158 =
                  let uu____60165 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60165  in
                FStar_Pervasives_Native.snd uu____60158
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____60192 = is_standard_constructor ctor  in
              if uu____60192
              then
                let uu____60196 =
                  let uu____60203 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60203  in
                FStar_Pervasives_Native.snd uu____60196
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
              | (uu____60236,uu____60237) ->
                  let uu____60244 =
                    let uu____60247 =
                      let uu____60250 =
                        let uu____60251 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____60251  in
                      [uu____60250]  in
                    (FStar_Format.text name) :: uu____60247  in
                  FStar_Format.reduce1 uu____60244
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____60262 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____60262) es
               in
            let docs1 =
              let uu____60264 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____60264  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____60281 =
                  let uu____60284 =
                    let uu____60287 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____60287]  in
                  FStar_Format.hardline :: uu____60284  in
                FStar_Format.reduce uu____60281
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____60296 =
              let uu____60297 =
                let uu____60300 =
                  let uu____60303 =
                    let uu____60306 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____60306]  in
                  doc1 :: uu____60303  in
                pre :: uu____60300  in
              FStar_Format.combine FStar_Format.hardline uu____60297  in
            FStar_Format.parens uu____60296
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____60317::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____60319;
                    FStar_Extraction_ML_Syntax.loc = uu____60320;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____60322)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____60324;
                  FStar_Extraction_ML_Syntax.loc = uu____60325;_}::[])
                 when
                 let uu____60369 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____60369 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____60395;
                            FStar_Extraction_ML_Syntax.loc = uu____60396;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____60398;
                       FStar_Extraction_ML_Syntax.loc = uu____60399;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60457;
                   FStar_Extraction_ML_Syntax.loc = uu____60458;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60471;
                   FStar_Extraction_ML_Syntax.loc = uu____60472;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____60479 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____60490 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____60490)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____60495 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60495
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____60505 =
                   let uu____60508 =
                     let uu____60511 =
                       let uu____60514 =
                         let uu____60515 = ptsym currentModule f  in
                         FStar_Format.text uu____60515  in
                       [uu____60514]  in
                     (FStar_Format.text ".") :: uu____60511  in
                   e2 :: uu____60508  in
                 FStar_Format.reduce uu____60505)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____60551 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60551
              then
                let uu____60554 =
                  let uu____60557 =
                    let uu____60560 =
                      let uu____60563 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____60565 =
                              let uu____60568 =
                                let uu____60571 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____60571]  in
                              (FStar_Format.text " : ") :: uu____60568  in
                            FStar_Format.reduce1 uu____60565
                        | uu____60573 -> FStar_Format.text ""  in
                      [uu____60563; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____60560  in
                  (FStar_Format.text "(") :: uu____60557  in
                FStar_Format.reduce1 uu____60554
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____60592  ->
                   match uu____60592 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____60604 =
                let uu____60607 =
                  let uu____60610 = FStar_Format.reduce1 ids1  in
                  [uu____60610; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____60607  in
              FStar_Format.reduce1 uu____60604  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60619 =
                let uu____60622 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60626 =
                  let uu____60629 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____60629; FStar_Format.text "end"]  in
                uu____60622 :: uu____60626  in
              FStar_Format.combine FStar_Format.hardline uu____60619  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60638 =
                let uu____60641 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60645 =
                  let uu____60648 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60649 =
                    let uu____60652 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____60656 =
                      let uu____60659 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____60659; FStar_Format.text "end"]  in
                    uu____60652 :: uu____60656  in
                  uu____60648 :: uu____60649  in
                uu____60641 :: uu____60645  in
              FStar_Format.combine FStar_Format.hardline uu____60638  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____60698 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____60698 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____60705 =
              let uu____60708 =
                let uu____60711 =
                  let uu____60712 = ptctor currentModule exn  in
                  FStar_Format.text uu____60712  in
                [uu____60711]  in
              (FStar_Format.text "raise") :: uu____60708  in
            FStar_Format.reduce1 uu____60705
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____60724 =
              let uu____60727 =
                let uu____60730 =
                  let uu____60731 = ptctor currentModule exn  in
                  FStar_Format.text uu____60731  in
                let uu____60733 =
                  let uu____60736 =
                    let uu____60737 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____60737  in
                  [uu____60736]  in
                uu____60730 :: uu____60733  in
              (FStar_Format.text "raise") :: uu____60727  in
            FStar_Format.reduce1 uu____60724
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____60762 =
              let uu____60765 =
                let uu____60768 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____60769 =
                  let uu____60772 =
                    let uu____60775 =
                      let uu____60776 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____60776
                       in
                    [uu____60775]  in
                  (FStar_Format.text "with") :: uu____60772  in
                uu____60768 :: uu____60769  in
              (FStar_Format.text "try") :: uu____60765  in
            FStar_Format.combine FStar_Format.hardline uu____60762
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
          let uu____60800 =
            let uu____60814 = as_bin_op p  in FStar_Option.get uu____60814
             in
          match uu____60800 with
          | (uu____60843,prio,txt) ->
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
        let uu____60867 =
          let uu____60874 = as_uni_op p  in FStar_Option.get uu____60874  in
        match uu____60867 with
        | (uu____60889,txt) ->
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
          let uu____60902 = string_of_mlconstant c  in
          FStar_Format.text uu____60902
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____60938 =
            match uu____60938 with
            | (name,p) ->
                let uu____60948 =
                  let uu____60951 =
                    let uu____60952 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____60952  in
                  let uu____60958 =
                    let uu____60961 =
                      let uu____60964 = doc_of_pattern currentModule p  in
                      [uu____60964]  in
                    (FStar_Format.text "=") :: uu____60961  in
                  uu____60951 :: uu____60958  in
                FStar_Format.reduce1 uu____60948
             in
          let uu____60966 =
            let uu____60967 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____60967  in
          FStar_Format.cbrackets uu____60966
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____60981 = is_standard_constructor ctor  in
            if uu____60981
            then
              let uu____60985 =
                let uu____60992 = as_standard_constructor ctor  in
                FStar_Option.get uu____60992  in
              FStar_Pervasives_Native.snd uu____60985
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____61019 = is_standard_constructor ctor  in
            if uu____61019
            then
              let uu____61023 =
                let uu____61030 = as_standard_constructor ctor  in
                FStar_Option.get uu____61030  in
              FStar_Pervasives_Native.snd uu____61023
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____61059 =
                  let uu____61062 =
                    let uu____61063 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____61063  in
                  let uu____61064 =
                    let uu____61067 =
                      let uu____61070 = doc_of_pattern currentModule xs  in
                      [uu____61070]  in
                    (FStar_Format.text "::") :: uu____61067  in
                  uu____61062 :: uu____61064  in
                FStar_Format.reduce uu____61059
            | (uu____61072,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____61073)::[]) ->
                let uu____61080 =
                  let uu____61083 =
                    let uu____61086 =
                      let uu____61087 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____61087  in
                    [uu____61086]  in
                  (FStar_Format.text name) :: uu____61083  in
                FStar_Format.reduce1 uu____61080
            | uu____61088 ->
                let uu____61096 =
                  let uu____61099 =
                    let uu____61102 =
                      let uu____61103 =
                        let uu____61104 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____61104
                         in
                      FStar_Format.parens uu____61103  in
                    [uu____61102]  in
                  (FStar_Format.text name) :: uu____61099  in
                FStar_Format.reduce1 uu____61096
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____61119 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____61119
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61132  ->
      match uu____61132 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____61142 =
                  let uu____61145 =
                    let uu____61148 = doc_of_pattern currentModule p  in
                    [uu____61148]  in
                  (FStar_Format.text "|") :: uu____61145  in
                FStar_Format.reduce1 uu____61142
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____61152 =
                  let uu____61155 =
                    let uu____61158 = doc_of_pattern currentModule p  in
                    [uu____61158; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____61155  in
                FStar_Format.reduce1 uu____61152
             in
          let uu____61161 =
            let uu____61164 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____61167 =
              let uu____61170 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____61170; FStar_Format.text "end"]  in
            uu____61164 :: uu____61167  in
          FStar_Format.combine FStar_Format.hardline uu____61161

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61173  ->
      match uu____61173 with
      | (rec_,top_level,lets) ->
          let for1 uu____61198 =
            match uu____61198 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____61201;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____61203;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____61219 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____61219
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____61222::uu____61223,uu____61224) ->
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
                                let uu____61248 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____61248
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____61267 =
                  let uu____61270 =
                    let uu____61273 = FStar_Format.reduce1 ids  in
                    [uu____61273; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____61270  in
                FStar_Format.reduce1 uu____61267
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
  fun uu____61299  ->
    match uu____61299 with
    | (lineno,file) ->
        let uu____61306 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____61306
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
      let for1 uu____61358 =
        match uu____61358 with
        | (uu____61381,x,mangle_opt,tparams,uu____61385,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____61420 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____61431 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____61431
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____61458 =
                    match uu____61458 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____61471 =
                    let uu____61472 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____61472
                     in
                  FStar_Format.cbrackets uu____61471
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____61513 =
                    match uu____61513 with
                    | (name,tys) ->
                        let uu____61544 = FStar_List.split tys  in
                        (match uu____61544 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____61567 ->
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
              let uu____61598 =
                let uu____61601 =
                  let uu____61604 =
                    let uu____61605 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____61605  in
                  [uu____61604]  in
                tparams1 :: uu____61601  in
              FStar_Format.reduce1 uu____61598  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____61614 =
                   let uu____61617 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____61617; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____61614)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____61625 =
            let uu____61628 =
              let uu____61631 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____61631]  in
            (FStar_Format.text "type") :: uu____61628  in
          FStar_Format.reduce1 uu____61625
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
          let uu____61667 =
            let uu____61670 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____61673 =
              let uu____61676 = doc_of_sig currentModule subsig  in
              let uu____61677 =
                let uu____61680 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____61680]  in
              uu____61676 :: uu____61677  in
            uu____61670 :: uu____61673  in
          FStar_Format.combine FStar_Format.hardline uu____61667
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____61700 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____61700  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____61705,ty)) ->
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
            let uu____61784 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____61784  in
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
          let uu____61800 =
            let uu____61803 =
              let uu____61806 =
                let uu____61809 =
                  let uu____61812 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____61812]  in
                (FStar_Format.text "=") :: uu____61809  in
              (FStar_Format.text "_") :: uu____61806  in
            (FStar_Format.text "let") :: uu____61803  in
          FStar_Format.reduce1 uu____61800
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____61842 ->
                  FStar_Format.empty
              | uu____61843 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____61856  ->
    match uu____61856 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____61926 =
          match uu____61926 with
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
                  (fun uu____61986  ->
                     match uu____61986 with
                     | (s,uu____61992) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____62013 =
                let uu____62016 =
                  let uu____62019 =
                    let uu____62022 = FStar_Format.reduce sub3  in
                    [uu____62022;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____62019
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____62016
                 in
              FStar_Format.reduce uu____62013
        
        and for1_mod istop uu____62025 =
          match uu____62025 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____62107 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____62128 =
                  let uu____62131 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____62131
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
                FStar_Format.reduce1 uu____62128  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____62162  ->
                     match uu____62162 with
                     | (uu____62167,m) -> doc_of_mod target_mod_name m)
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
                let uu____62193 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____62193
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____62201 =
                let uu____62204 =
                  let uu____62207 =
                    let uu____62210 =
                      let uu____62213 =
                        let uu____62216 =
                          let uu____62219 = FStar_Format.reduce sub3  in
                          [uu____62219;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____62216
                         in
                      FStar_Format.hardline :: uu____62213  in
                    FStar_List.append maybe_open_pervasives uu____62210  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____62207
                   in
                FStar_List.append prefix1 uu____62204  in
              FStar_All.pipe_left FStar_Format.reduce uu____62201
         in
        let docs =
          FStar_List.map
            (fun uu____62263  ->
               match uu____62263 with
               | (x,s,m) ->
                   let uu____62320 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____62322 = for1_mod true (x, s, m)  in
                   (uu____62320, uu____62322)) mllib
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
        let uu____62365 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____62365 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____62381 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____62381 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  