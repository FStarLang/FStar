open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____62693 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____62704 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____62715 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____62726 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____62737 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____62753 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____62764 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____62776 -> false
  
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
    | ([],uu____62974) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____62998,uu____62999) -> false
  
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
                  let uu____63084 = FStar_Util.first_N cg_len ns  in
                  match uu____63084 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____63128 =
                           let uu____63132 =
                             let uu____63136 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____63136]  in
                           FStar_List.append pfx uu____63132  in
                         FStar_Pervasives_Native.Some uu____63128
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
      let uu____63182 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____63182 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____63198 ->
          let uu____63200 = x  in
          (match uu____63200 with
           | (ns,x1) ->
               let uu____63211 = path_of_ns currentModule ns  in
               (uu____63211, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____63229 =
      let uu____63231 =
        let uu____63233 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____63233  in
      let uu____63236 = FStar_String.get s (Prims.parse_int "0")  in
      uu____63231 <> uu____63236  in
    if uu____63229 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____63272 = mlpath_of_mlpath currentModule mlp  in
         match uu____63272 with
         | (p,s) ->
             let uu____63284 =
               let uu____63288 =
                 let uu____63292 = ptsym_of_symbol s  in [uu____63292]  in
               FStar_List.append p uu____63288  in
             FStar_String.concat "." uu____63284)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____63313 = mlpath_of_mlpath currentModule mlp  in
      match uu____63313 with
      | (p,s) ->
          let s1 =
            let uu____63327 =
              let uu____63329 =
                let uu____63331 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____63331  in
              let uu____63334 = FStar_String.get s (Prims.parse_int "0")  in
              uu____63329 <> uu____63334  in
            if uu____63327 then Prims.op_Hat "U__" s else s  in
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
  fun uu____63697  ->
    let op_minus =
      let uu____63700 =
        let uu____63702 = FStar_Options.codegen ()  in
        uu____63702 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____63700 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____63751 . unit -> 'Auu____63751 Prims.list =
  fun uu____63754  -> [] 
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
  fun uu____63849  ->
    match uu____63849 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____63908  ->
               match uu____63908 with | (y,uu____63924,uu____63925) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____63963 = as_bin_op p  in
    uu____63963 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64020  ->
    match uu____64020 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____64048 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____64066  ->
               match uu____64066 with | (y,uu____64075) -> x = y) uu____64048
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64096 = as_uni_op p  in
    uu____64096 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64140  ->
    match uu____64140 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____64177  ->
               match uu____64177 with | (y,uu____64186) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64207 = as_standard_constructor p  in
    uu____64207 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____64257  ->
    fun inner  ->
      fun doc1  ->
        match uu____64257 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____64323 = _inner  in
              match uu____64323 with
              | (pi,fi) ->
                  let uu____64334 = _outer  in
                  (match uu____64334 with
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
                           | (uu____64352,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____64354,uu____64355) -> false)))
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
    fun uu___543_64394  ->
      if uu___543_64394 = 92
      then "\\\\"
      else
        if uu___543_64394 = 32
        then " "
        else
          if uu___543_64394 = 8
          then "\\b"
          else
            if uu___543_64394 = 9
            then "\\t"
            else
              if uu___543_64394 = 13
              then "\\r"
              else
                if uu___543_64394 = 10
                then "\\n"
                else
                  if uu___543_64394 = 39
                  then "\\'"
                  else
                    if uu___543_64394 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_64394
                      then FStar_Util.string_of_char uu___543_64394
                      else
                        if FStar_Util.is_punctuation uu___543_64394
                        then FStar_Util.string_of_char uu___543_64394
                        else
                          if FStar_Util.is_symbol uu___543_64394
                          then FStar_Util.string_of_char uu___543_64394
                          else fallback uu___543_64394
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____64441 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____64441
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
        (s,FStar_Pervasives_Native.Some (uu____64505,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64519,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____64551 =
          let uu____64553 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____64553 "\""  in
        Prims.op_Hat "\"" uu____64551
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____64559 =
          let uu____64561 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____64561 "\""  in
        Prims.op_Hat "\"" uu____64559
    | uu____64565 ->
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
              let uu____64624 =
                let uu____64625 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____64625  in
              FStar_Format.parens uu____64624  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____64635 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____64641 =
                    let uu____64642 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____64642  in
                  FStar_Format.parens uu____64641
               in
            let name1 = ptsym currentModule name  in
            let uu____64646 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____64646
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____64648,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____64652 =
              let uu____64653 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____64653  in
            maybe_paren outer t_prio_fun uu____64652
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____64655 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64655
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
        let uu____64667 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____64667

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
            let uu____64760 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64760
            then
              let uu____64763 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____64763
            else
              (let uu____64767 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____64767)
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
            let uu____64781 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____64781
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____64783 = string_of_mlconstant c  in
            FStar_Format.text uu____64783
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____64788 = ptsym currentModule path  in
            FStar_Format.text uu____64788
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____64822 =
              match uu____64822 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____64833 =
                    let uu____64836 =
                      let uu____64837 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____64837  in
                    [uu____64836; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____64833
               in
            let uu____64844 =
              let uu____64845 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____64845  in
            FStar_Format.cbrackets uu____64844
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____64859 = is_standard_constructor ctor  in
              if uu____64859
              then
                let uu____64863 =
                  let uu____64870 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64870  in
                FStar_Pervasives_Native.snd uu____64863
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____64897 = is_standard_constructor ctor  in
              if uu____64897
              then
                let uu____64901 =
                  let uu____64908 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64908  in
                FStar_Pervasives_Native.snd uu____64901
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
              | (uu____64941,uu____64942) ->
                  let uu____64949 =
                    let uu____64952 =
                      let uu____64955 =
                        let uu____64956 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____64956  in
                      [uu____64955]  in
                    (FStar_Format.text name) :: uu____64952  in
                  FStar_Format.reduce1 uu____64949
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____64967 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____64967) es
               in
            let docs1 =
              let uu____64969 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____64969  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____64986 =
                  let uu____64989 =
                    let uu____64992 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____64992]  in
                  FStar_Format.hardline :: uu____64989  in
                FStar_Format.reduce uu____64986
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____65001 =
              let uu____65002 =
                let uu____65005 =
                  let uu____65008 =
                    let uu____65011 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____65011]  in
                  doc1 :: uu____65008  in
                pre :: uu____65005  in
              FStar_Format.combine FStar_Format.hardline uu____65002  in
            FStar_Format.parens uu____65001
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____65022::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____65024;
                    FStar_Extraction_ML_Syntax.loc = uu____65025;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____65027)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____65029;
                  FStar_Extraction_ML_Syntax.loc = uu____65030;_}::[])
                 when
                 let uu____65074 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____65074 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____65100;
                            FStar_Extraction_ML_Syntax.loc = uu____65101;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____65103;
                       FStar_Extraction_ML_Syntax.loc = uu____65104;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65162;
                   FStar_Extraction_ML_Syntax.loc = uu____65163;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65176;
                   FStar_Extraction_ML_Syntax.loc = uu____65177;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____65184 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____65195 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____65195)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____65200 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65200
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____65210 =
                   let uu____65213 =
                     let uu____65216 =
                       let uu____65219 =
                         let uu____65220 = ptsym currentModule f  in
                         FStar_Format.text uu____65220  in
                       [uu____65219]  in
                     (FStar_Format.text ".") :: uu____65216  in
                   e2 :: uu____65213  in
                 FStar_Format.reduce uu____65210)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____65256 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65256
              then
                let uu____65259 =
                  let uu____65262 =
                    let uu____65265 =
                      let uu____65268 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____65270 =
                              let uu____65273 =
                                let uu____65276 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____65276]  in
                              (FStar_Format.text " : ") :: uu____65273  in
                            FStar_Format.reduce1 uu____65270
                        | uu____65278 -> FStar_Format.text ""  in
                      [uu____65268; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____65265  in
                  (FStar_Format.text "(") :: uu____65262  in
                FStar_Format.reduce1 uu____65259
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____65297  ->
                   match uu____65297 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____65309 =
                let uu____65312 =
                  let uu____65315 = FStar_Format.reduce1 ids1  in
                  [uu____65315; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____65312  in
              FStar_Format.reduce1 uu____65309  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65324 =
                let uu____65327 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65331 =
                  let uu____65334 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____65334; FStar_Format.text "end"]  in
                uu____65327 :: uu____65331  in
              FStar_Format.combine FStar_Format.hardline uu____65324  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65343 =
                let uu____65346 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65350 =
                  let uu____65353 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____65354 =
                    let uu____65357 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____65361 =
                      let uu____65364 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____65364; FStar_Format.text "end"]  in
                    uu____65357 :: uu____65361  in
                  uu____65353 :: uu____65354  in
                uu____65346 :: uu____65350  in
              FStar_Format.combine FStar_Format.hardline uu____65343  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____65403 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____65403 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____65410 =
              let uu____65413 =
                let uu____65416 =
                  let uu____65417 = ptctor currentModule exn  in
                  FStar_Format.text uu____65417  in
                [uu____65416]  in
              (FStar_Format.text "raise") :: uu____65413  in
            FStar_Format.reduce1 uu____65410
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____65429 =
              let uu____65432 =
                let uu____65435 =
                  let uu____65436 = ptctor currentModule exn  in
                  FStar_Format.text uu____65436  in
                let uu____65438 =
                  let uu____65441 =
                    let uu____65442 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____65442  in
                  [uu____65441]  in
                uu____65435 :: uu____65438  in
              (FStar_Format.text "raise") :: uu____65432  in
            FStar_Format.reduce1 uu____65429
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____65467 =
              let uu____65470 =
                let uu____65473 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____65474 =
                  let uu____65477 =
                    let uu____65480 =
                      let uu____65481 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____65481
                       in
                    [uu____65480]  in
                  (FStar_Format.text "with") :: uu____65477  in
                uu____65473 :: uu____65474  in
              (FStar_Format.text "try") :: uu____65470  in
            FStar_Format.combine FStar_Format.hardline uu____65467
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
          let uu____65505 =
            let uu____65519 = as_bin_op p  in FStar_Option.get uu____65519
             in
          match uu____65505 with
          | (uu____65548,prio,txt) ->
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
        let uu____65572 =
          let uu____65579 = as_uni_op p  in FStar_Option.get uu____65579  in
        match uu____65572 with
        | (uu____65594,txt) ->
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
          let uu____65607 = string_of_mlconstant c  in
          FStar_Format.text uu____65607
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____65643 =
            match uu____65643 with
            | (name,p) ->
                let uu____65653 =
                  let uu____65656 =
                    let uu____65657 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____65657  in
                  let uu____65663 =
                    let uu____65666 =
                      let uu____65669 = doc_of_pattern currentModule p  in
                      [uu____65669]  in
                    (FStar_Format.text "=") :: uu____65666  in
                  uu____65656 :: uu____65663  in
                FStar_Format.reduce1 uu____65653
             in
          let uu____65671 =
            let uu____65672 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____65672  in
          FStar_Format.cbrackets uu____65671
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____65686 = is_standard_constructor ctor  in
            if uu____65686
            then
              let uu____65690 =
                let uu____65697 = as_standard_constructor ctor  in
                FStar_Option.get uu____65697  in
              FStar_Pervasives_Native.snd uu____65690
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____65724 = is_standard_constructor ctor  in
            if uu____65724
            then
              let uu____65728 =
                let uu____65735 = as_standard_constructor ctor  in
                FStar_Option.get uu____65735  in
              FStar_Pervasives_Native.snd uu____65728
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____65764 =
                  let uu____65767 =
                    let uu____65768 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____65768  in
                  let uu____65769 =
                    let uu____65772 =
                      let uu____65775 = doc_of_pattern currentModule xs  in
                      [uu____65775]  in
                    (FStar_Format.text "::") :: uu____65772  in
                  uu____65767 :: uu____65769  in
                FStar_Format.reduce uu____65764
            | (uu____65777,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____65778)::[]) ->
                let uu____65785 =
                  let uu____65788 =
                    let uu____65791 =
                      let uu____65792 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____65792  in
                    [uu____65791]  in
                  (FStar_Format.text name) :: uu____65788  in
                FStar_Format.reduce1 uu____65785
            | uu____65793 ->
                let uu____65801 =
                  let uu____65804 =
                    let uu____65807 =
                      let uu____65808 =
                        let uu____65809 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____65809
                         in
                      FStar_Format.parens uu____65808  in
                    [uu____65807]  in
                  (FStar_Format.text name) :: uu____65804  in
                FStar_Format.reduce1 uu____65801
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____65824 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____65824
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65837  ->
      match uu____65837 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____65847 =
                  let uu____65850 =
                    let uu____65853 = doc_of_pattern currentModule p  in
                    [uu____65853]  in
                  (FStar_Format.text "|") :: uu____65850  in
                FStar_Format.reduce1 uu____65847
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____65857 =
                  let uu____65860 =
                    let uu____65863 = doc_of_pattern currentModule p  in
                    [uu____65863; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____65860  in
                FStar_Format.reduce1 uu____65857
             in
          let uu____65866 =
            let uu____65869 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____65872 =
              let uu____65875 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____65875; FStar_Format.text "end"]  in
            uu____65869 :: uu____65872  in
          FStar_Format.combine FStar_Format.hardline uu____65866

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65878  ->
      match uu____65878 with
      | (rec_,top_level,lets) ->
          let for1 uu____65903 =
            match uu____65903 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____65906;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____65908;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____65924 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____65924
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____65927::uu____65928,uu____65929) ->
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
                                let uu____65953 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____65953
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____65972 =
                  let uu____65975 =
                    let uu____65978 = FStar_Format.reduce1 ids  in
                    [uu____65978; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____65975  in
                FStar_Format.reduce1 uu____65972
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
  fun uu____66004  ->
    match uu____66004 with
    | (lineno,file) ->
        let uu____66011 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____66011
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
      let for1 uu____66063 =
        match uu____66063 with
        | (uu____66086,x,mangle_opt,tparams,uu____66090,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____66125 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____66136 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____66136
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____66163 =
                    match uu____66163 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____66176 =
                    let uu____66177 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____66177
                     in
                  FStar_Format.cbrackets uu____66176
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____66218 =
                    match uu____66218 with
                    | (name,tys) ->
                        let uu____66249 = FStar_List.split tys  in
                        (match uu____66249 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____66272 ->
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
              let uu____66303 =
                let uu____66306 =
                  let uu____66309 =
                    let uu____66310 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____66310  in
                  [uu____66309]  in
                tparams1 :: uu____66306  in
              FStar_Format.reduce1 uu____66303  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____66319 =
                   let uu____66322 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____66322; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____66319)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____66330 =
            let uu____66333 =
              let uu____66336 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____66336]  in
            (FStar_Format.text "type") :: uu____66333  in
          FStar_Format.reduce1 uu____66330
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
          let uu____66372 =
            let uu____66375 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____66378 =
              let uu____66381 = doc_of_sig currentModule subsig  in
              let uu____66382 =
                let uu____66385 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____66385]  in
              uu____66381 :: uu____66382  in
            uu____66375 :: uu____66378  in
          FStar_Format.combine FStar_Format.hardline uu____66372
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____66405 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____66405  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____66410,ty)) ->
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
            let uu____66489 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____66489  in
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
          let uu____66505 =
            let uu____66508 =
              let uu____66511 =
                let uu____66514 =
                  let uu____66517 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____66517]  in
                (FStar_Format.text "=") :: uu____66514  in
              (FStar_Format.text "_") :: uu____66511  in
            (FStar_Format.text "let") :: uu____66508  in
          FStar_Format.reduce1 uu____66505
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____66547 ->
                  FStar_Format.empty
              | uu____66548 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____66561  ->
    match uu____66561 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____66631 =
          match uu____66631 with
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
                  (fun uu____66691  ->
                     match uu____66691 with
                     | (s,uu____66697) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____66718 =
                let uu____66721 =
                  let uu____66724 =
                    let uu____66727 = FStar_Format.reduce sub3  in
                    [uu____66727;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____66724
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____66721
                 in
              FStar_Format.reduce uu____66718
        
        and for1_mod istop uu____66730 =
          match uu____66730 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____66812 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____66833 =
                  let uu____66836 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____66836
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
                FStar_Format.reduce1 uu____66833  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66867  ->
                     match uu____66867 with
                     | (uu____66872,m) -> doc_of_mod target_mod_name m)
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
                let uu____66898 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____66898
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____66906 =
                let uu____66909 =
                  let uu____66912 =
                    let uu____66915 =
                      let uu____66918 =
                        let uu____66921 =
                          let uu____66924 = FStar_Format.reduce sub3  in
                          [uu____66924;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____66921
                         in
                      FStar_Format.hardline :: uu____66918  in
                    FStar_List.append maybe_open_pervasives uu____66915  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____66912
                   in
                FStar_List.append prefix1 uu____66909  in
              FStar_All.pipe_left FStar_Format.reduce uu____66906
         in
        let docs =
          FStar_List.map
            (fun uu____66968  ->
               match uu____66968 with
               | (x,s,m) ->
                   let uu____67025 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____67027 = for1_mod true (x, s, m)  in
                   (uu____67025, uu____67027)) mllib
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
        let uu____67070 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____67070 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67086 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____67086 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  