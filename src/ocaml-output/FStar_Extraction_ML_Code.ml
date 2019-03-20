open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____57999 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____58010 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____58021 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____58032 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____58043 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____58059 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____58070 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____58082 -> false
  
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
    | ([],uu____58279) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____58303,uu____58304) -> false
  
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
                  let uu____58385 = FStar_Util.first_N cg_len ns  in
                  match uu____58385 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____58425 =
                           let uu____58429 =
                             let uu____58433 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____58433]  in
                           FStar_List.append pfx uu____58429  in
                         FStar_Pervasives_Native.Some uu____58425
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
      let uu____58479 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____58479 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____58495 ->
          let uu____58497 = x  in
          (match uu____58497 with
           | (ns,x1) ->
               let uu____58508 = path_of_ns currentModule ns  in
               (uu____58508, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____58526 =
      let uu____58528 =
        let uu____58530 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____58530  in
      let uu____58533 = FStar_String.get s (Prims.parse_int "0")  in
      uu____58528 <> uu____58533  in
    if uu____58526 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____58569 = mlpath_of_mlpath currentModule mlp  in
         match uu____58569 with
         | (p,s) ->
             let uu____58581 =
               let uu____58585 =
                 let uu____58589 = ptsym_of_symbol s  in [uu____58589]  in
               FStar_List.append p uu____58585  in
             FStar_String.concat "." uu____58581)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____58610 = mlpath_of_mlpath currentModule mlp  in
      match uu____58610 with
      | (p,s) ->
          let s1 =
            let uu____58624 =
              let uu____58626 =
                let uu____58628 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____58628  in
              let uu____58631 = FStar_String.get s (Prims.parse_int "0")  in
              uu____58626 <> uu____58631  in
            if uu____58624 then Prims.op_Hat "U__" s else s  in
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
  fun uu____58994  ->
    let op_minus =
      let uu____58997 =
        let uu____58999 = FStar_Options.codegen ()  in
        uu____58999 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____58997 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____59048 . unit -> 'Auu____59048 Prims.list =
  fun uu____59051  -> [] 
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
  fun uu____59146  ->
    match uu____59146 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59205  ->
               match uu____59205 with | (y,uu____59221,uu____59222) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59260 = as_bin_op p  in
    uu____59260 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59317  ->
    match uu____59317 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____59345 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____59363  ->
               match uu____59363 with | (y,uu____59372) -> x = y) uu____59345
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59393 = as_uni_op p  in
    uu____59393 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59437  ->
    match uu____59437 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59474  ->
               match uu____59474 with | (y,uu____59483) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59504 = as_standard_constructor p  in
    uu____59504 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____59554  ->
    fun inner  ->
      fun doc1  ->
        match uu____59554 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____59620 = _inner  in
              match uu____59620 with
              | (pi,fi) ->
                  let uu____59631 = _outer  in
                  (match uu____59631 with
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
                           | (uu____59649,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____59651,uu____59652) -> false)))
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
    fun uu___543_59691  ->
      if uu___543_59691 = 92
      then "\\\\"
      else
        if uu___543_59691 = 32
        then " "
        else
          if uu___543_59691 = 8
          then "\\b"
          else
            if uu___543_59691 = 9
            then "\\t"
            else
              if uu___543_59691 = 13
              then "\\r"
              else
                if uu___543_59691 = 10
                then "\\n"
                else
                  if uu___543_59691 = 39
                  then "\\'"
                  else
                    if uu___543_59691 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_59691
                      then FStar_Util.string_of_char uu___543_59691
                      else
                        if FStar_Util.is_punctuation uu___543_59691
                        then FStar_Util.string_of_char uu___543_59691
                        else
                          if FStar_Util.is_symbol uu___543_59691
                          then FStar_Util.string_of_char uu___543_59691
                          else fallback uu___543_59691
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____59738 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____59738
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
        (s,FStar_Pervasives_Native.Some (uu____59780,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____59794,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____59826 =
          let uu____59828 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____59828 "\""  in
        Prims.op_Hat "\"" uu____59826
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____59834 =
          let uu____59836 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____59836 "\""  in
        Prims.op_Hat "\"" uu____59834
    | uu____59840 ->
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
              let uu____59899 =
                let uu____59900 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____59900  in
              FStar_Format.parens uu____59899  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____59910 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____59916 =
                    let uu____59917 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____59917  in
                  FStar_Format.parens uu____59916
               in
            let name1 = ptsym currentModule name  in
            let uu____59921 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____59921
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____59923,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____59927 =
              let uu____59928 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____59928  in
            maybe_paren outer t_prio_fun uu____59927
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____59930 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____59930
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
        let uu____59942 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____59942

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
            let uu____60035 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60035
            then
              let uu____60038 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____60038
            else
              (let uu____60042 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____60042)
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
            let uu____60056 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____60056
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____60058 = string_of_mlconstant c  in
            FStar_Format.text uu____60058
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____60063 = ptsym currentModule path  in
            FStar_Format.text uu____60063
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____60097 =
              match uu____60097 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60108 =
                    let uu____60111 =
                      let uu____60112 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____60112  in
                    [uu____60111; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____60108
               in
            let uu____60119 =
              let uu____60120 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____60120  in
            FStar_Format.cbrackets uu____60119
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____60134 = is_standard_constructor ctor  in
              if uu____60134
              then
                let uu____60138 =
                  let uu____60145 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60145  in
                FStar_Pervasives_Native.snd uu____60138
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____60172 = is_standard_constructor ctor  in
              if uu____60172
              then
                let uu____60176 =
                  let uu____60183 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60183  in
                FStar_Pervasives_Native.snd uu____60176
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
              | (uu____60216,uu____60217) ->
                  let uu____60224 =
                    let uu____60227 =
                      let uu____60230 =
                        let uu____60231 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____60231  in
                      [uu____60230]  in
                    (FStar_Format.text name) :: uu____60227  in
                  FStar_Format.reduce1 uu____60224
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____60242 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____60242) es
               in
            let docs1 =
              let uu____60244 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____60244  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____60261 =
                  let uu____60264 =
                    let uu____60267 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____60267]  in
                  FStar_Format.hardline :: uu____60264  in
                FStar_Format.reduce uu____60261
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____60276 =
              let uu____60277 =
                let uu____60280 =
                  let uu____60283 =
                    let uu____60286 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____60286]  in
                  doc1 :: uu____60283  in
                pre :: uu____60280  in
              FStar_Format.combine FStar_Format.hardline uu____60277  in
            FStar_Format.parens uu____60276
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____60297::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____60299;
                    FStar_Extraction_ML_Syntax.loc = uu____60300;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____60302)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____60304;
                  FStar_Extraction_ML_Syntax.loc = uu____60305;_}::[])
                 when
                 let uu____60349 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____60349 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____60375;
                            FStar_Extraction_ML_Syntax.loc = uu____60376;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____60378;
                       FStar_Extraction_ML_Syntax.loc = uu____60379;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60437;
                   FStar_Extraction_ML_Syntax.loc = uu____60438;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60451;
                   FStar_Extraction_ML_Syntax.loc = uu____60452;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____60459 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____60470 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____60470)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____60475 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60475
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____60485 =
                   let uu____60488 =
                     let uu____60491 =
                       let uu____60494 =
                         let uu____60495 = ptsym currentModule f  in
                         FStar_Format.text uu____60495  in
                       [uu____60494]  in
                     (FStar_Format.text ".") :: uu____60491  in
                   e2 :: uu____60488  in
                 FStar_Format.reduce uu____60485)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____60531 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60531
              then
                let uu____60534 =
                  let uu____60537 =
                    let uu____60540 =
                      let uu____60543 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____60545 =
                              let uu____60548 =
                                let uu____60551 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____60551]  in
                              (FStar_Format.text " : ") :: uu____60548  in
                            FStar_Format.reduce1 uu____60545
                        | uu____60553 -> FStar_Format.text ""  in
                      [uu____60543; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____60540  in
                  (FStar_Format.text "(") :: uu____60537  in
                FStar_Format.reduce1 uu____60534
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____60572  ->
                   match uu____60572 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____60584 =
                let uu____60587 =
                  let uu____60590 = FStar_Format.reduce1 ids1  in
                  [uu____60590; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____60587  in
              FStar_Format.reduce1 uu____60584  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60599 =
                let uu____60602 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60606 =
                  let uu____60609 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____60609; FStar_Format.text "end"]  in
                uu____60602 :: uu____60606  in
              FStar_Format.combine FStar_Format.hardline uu____60599  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
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
                  let uu____60629 =
                    let uu____60632 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____60636 =
                      let uu____60639 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____60639; FStar_Format.text "end"]  in
                    uu____60632 :: uu____60636  in
                  uu____60628 :: uu____60629  in
                uu____60621 :: uu____60625  in
              FStar_Format.combine FStar_Format.hardline uu____60618  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____60678 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____60678 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____60685 =
              let uu____60688 =
                let uu____60691 =
                  let uu____60692 = ptctor currentModule exn  in
                  FStar_Format.text uu____60692  in
                [uu____60691]  in
              (FStar_Format.text "raise") :: uu____60688  in
            FStar_Format.reduce1 uu____60685
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____60704 =
              let uu____60707 =
                let uu____60710 =
                  let uu____60711 = ptctor currentModule exn  in
                  FStar_Format.text uu____60711  in
                let uu____60713 =
                  let uu____60716 =
                    let uu____60717 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____60717  in
                  [uu____60716]  in
                uu____60710 :: uu____60713  in
              (FStar_Format.text "raise") :: uu____60707  in
            FStar_Format.reduce1 uu____60704
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____60742 =
              let uu____60745 =
                let uu____60748 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____60749 =
                  let uu____60752 =
                    let uu____60755 =
                      let uu____60756 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____60756
                       in
                    [uu____60755]  in
                  (FStar_Format.text "with") :: uu____60752  in
                uu____60748 :: uu____60749  in
              (FStar_Format.text "try") :: uu____60745  in
            FStar_Format.combine FStar_Format.hardline uu____60742
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
          let uu____60780 =
            let uu____60794 = as_bin_op p  in FStar_Option.get uu____60794
             in
          match uu____60780 with
          | (uu____60823,prio,txt) ->
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
        let uu____60847 =
          let uu____60854 = as_uni_op p  in FStar_Option.get uu____60854  in
        match uu____60847 with
        | (uu____60869,txt) ->
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
          let uu____60882 = string_of_mlconstant c  in
          FStar_Format.text uu____60882
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____60918 =
            match uu____60918 with
            | (name,p) ->
                let uu____60928 =
                  let uu____60931 =
                    let uu____60932 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____60932  in
                  let uu____60938 =
                    let uu____60941 =
                      let uu____60944 = doc_of_pattern currentModule p  in
                      [uu____60944]  in
                    (FStar_Format.text "=") :: uu____60941  in
                  uu____60931 :: uu____60938  in
                FStar_Format.reduce1 uu____60928
             in
          let uu____60946 =
            let uu____60947 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____60947  in
          FStar_Format.cbrackets uu____60946
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____60961 = is_standard_constructor ctor  in
            if uu____60961
            then
              let uu____60965 =
                let uu____60972 = as_standard_constructor ctor  in
                FStar_Option.get uu____60972  in
              FStar_Pervasives_Native.snd uu____60965
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____60999 = is_standard_constructor ctor  in
            if uu____60999
            then
              let uu____61003 =
                let uu____61010 = as_standard_constructor ctor  in
                FStar_Option.get uu____61010  in
              FStar_Pervasives_Native.snd uu____61003
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____61039 =
                  let uu____61042 =
                    let uu____61043 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____61043  in
                  let uu____61044 =
                    let uu____61047 =
                      let uu____61050 = doc_of_pattern currentModule xs  in
                      [uu____61050]  in
                    (FStar_Format.text "::") :: uu____61047  in
                  uu____61042 :: uu____61044  in
                FStar_Format.reduce uu____61039
            | (uu____61052,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____61053)::[]) ->
                let uu____61060 =
                  let uu____61063 =
                    let uu____61066 =
                      let uu____61067 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____61067  in
                    [uu____61066]  in
                  (FStar_Format.text name) :: uu____61063  in
                FStar_Format.reduce1 uu____61060
            | uu____61068 ->
                let uu____61076 =
                  let uu____61079 =
                    let uu____61082 =
                      let uu____61083 =
                        let uu____61084 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____61084
                         in
                      FStar_Format.parens uu____61083  in
                    [uu____61082]  in
                  (FStar_Format.text name) :: uu____61079  in
                FStar_Format.reduce1 uu____61076
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____61099 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____61099
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61112  ->
      match uu____61112 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____61122 =
                  let uu____61125 =
                    let uu____61128 = doc_of_pattern currentModule p  in
                    [uu____61128]  in
                  (FStar_Format.text "|") :: uu____61125  in
                FStar_Format.reduce1 uu____61122
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____61132 =
                  let uu____61135 =
                    let uu____61138 = doc_of_pattern currentModule p  in
                    [uu____61138; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____61135  in
                FStar_Format.reduce1 uu____61132
             in
          let uu____61141 =
            let uu____61144 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____61147 =
              let uu____61150 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____61150; FStar_Format.text "end"]  in
            uu____61144 :: uu____61147  in
          FStar_Format.combine FStar_Format.hardline uu____61141

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61153  ->
      match uu____61153 with
      | (rec_,top_level,lets) ->
          let for1 uu____61178 =
            match uu____61178 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____61181;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____61183;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____61199 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____61199
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____61202::uu____61203,uu____61204) ->
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
                                let uu____61228 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____61228
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____61247 =
                  let uu____61250 =
                    let uu____61253 = FStar_Format.reduce1 ids  in
                    [uu____61253; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____61250  in
                FStar_Format.reduce1 uu____61247
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
  fun uu____61279  ->
    match uu____61279 with
    | (lineno,file) ->
        let uu____61286 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____61286
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
      let for1 uu____61338 =
        match uu____61338 with
        | (uu____61361,x,mangle_opt,tparams,uu____61365,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____61400 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____61411 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____61411
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____61438 =
                    match uu____61438 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____61451 =
                    let uu____61452 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____61452
                     in
                  FStar_Format.cbrackets uu____61451
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____61493 =
                    match uu____61493 with
                    | (name,tys) ->
                        let uu____61524 = FStar_List.split tys  in
                        (match uu____61524 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____61547 ->
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
              let uu____61578 =
                let uu____61581 =
                  let uu____61584 =
                    let uu____61585 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____61585  in
                  [uu____61584]  in
                tparams1 :: uu____61581  in
              FStar_Format.reduce1 uu____61578  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____61594 =
                   let uu____61597 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____61597; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____61594)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____61605 =
            let uu____61608 =
              let uu____61611 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____61611]  in
            (FStar_Format.text "type") :: uu____61608  in
          FStar_Format.reduce1 uu____61605
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
          let uu____61647 =
            let uu____61650 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____61653 =
              let uu____61656 = doc_of_sig currentModule subsig  in
              let uu____61657 =
                let uu____61660 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____61660]  in
              uu____61656 :: uu____61657  in
            uu____61650 :: uu____61653  in
          FStar_Format.combine FStar_Format.hardline uu____61647
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____61680 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____61680  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____61685,ty)) ->
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
            let uu____61764 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____61764  in
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
          let uu____61780 =
            let uu____61783 =
              let uu____61786 =
                let uu____61789 =
                  let uu____61792 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____61792]  in
                (FStar_Format.text "=") :: uu____61789  in
              (FStar_Format.text "_") :: uu____61786  in
            (FStar_Format.text "let") :: uu____61783  in
          FStar_Format.reduce1 uu____61780
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____61822 ->
                  FStar_Format.empty
              | uu____61823 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____61836  ->
    match uu____61836 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____61906 =
          match uu____61906 with
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
                  (fun uu____61966  ->
                     match uu____61966 with
                     | (s,uu____61972) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____61993 =
                let uu____61996 =
                  let uu____61999 =
                    let uu____62002 = FStar_Format.reduce sub3  in
                    [uu____62002;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____61999
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____61996
                 in
              FStar_Format.reduce uu____61993
        
        and for1_mod istop uu____62005 =
          match uu____62005 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____62087 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____62108 =
                  let uu____62111 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____62111
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
                FStar_Format.reduce1 uu____62108  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____62142  ->
                     match uu____62142 with
                     | (uu____62147,m) -> doc_of_mod target_mod_name m)
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
                let uu____62173 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____62173
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____62181 =
                let uu____62184 =
                  let uu____62187 =
                    let uu____62190 =
                      let uu____62193 =
                        let uu____62196 =
                          let uu____62199 = FStar_Format.reduce sub3  in
                          [uu____62199;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____62196
                         in
                      FStar_Format.hardline :: uu____62193  in
                    FStar_List.append maybe_open_pervasives uu____62190  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____62187
                   in
                FStar_List.append prefix1 uu____62184  in
              FStar_All.pipe_left FStar_Format.reduce uu____62181
         in
        let docs =
          FStar_List.map
            (fun uu____62243  ->
               match uu____62243 with
               | (x,s,m) ->
                   let uu____62300 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____62302 = for1_mod true (x, s, m)  in
                   (uu____62300, uu____62302)) mllib
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
        let uu____62345 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____62345 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____62361 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____62361 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  