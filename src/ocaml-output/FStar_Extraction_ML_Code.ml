open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____62624 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____62635 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____62646 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____62657 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____62668 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____62684 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____62695 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____62707 -> false
  
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
    | ([],uu____62905) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____62929,uu____62930) -> false
  
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
                  let uu____63015 = FStar_Util.first_N cg_len ns  in
                  match uu____63015 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____63059 =
                           let uu____63063 =
                             let uu____63067 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____63067]  in
                           FStar_List.append pfx uu____63063  in
                         FStar_Pervasives_Native.Some uu____63059
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
      let uu____63113 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____63113 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____63129 ->
          let uu____63131 = x  in
          (match uu____63131 with
           | (ns,x1) ->
               let uu____63142 = path_of_ns currentModule ns  in
               (uu____63142, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____63160 =
      let uu____63162 =
        let uu____63164 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____63164  in
      let uu____63167 = FStar_String.get s (Prims.parse_int "0")  in
      uu____63162 <> uu____63167  in
    if uu____63160 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____63203 = mlpath_of_mlpath currentModule mlp  in
         match uu____63203 with
         | (p,s) ->
             let uu____63215 =
               let uu____63219 =
                 let uu____63223 = ptsym_of_symbol s  in [uu____63223]  in
               FStar_List.append p uu____63219  in
             FStar_String.concat "." uu____63215)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____63244 = mlpath_of_mlpath currentModule mlp  in
      match uu____63244 with
      | (p,s) ->
          let s1 =
            let uu____63258 =
              let uu____63260 =
                let uu____63262 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____63262  in
              let uu____63265 = FStar_String.get s (Prims.parse_int "0")  in
              uu____63260 <> uu____63265  in
            if uu____63258 then Prims.op_Hat "U__" s else s  in
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
  fun uu____63628  ->
    let op_minus =
      let uu____63631 =
        let uu____63633 = FStar_Options.codegen ()  in
        uu____63633 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____63631 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____63682 . unit -> 'Auu____63682 Prims.list =
  fun uu____63685  -> [] 
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
  fun uu____63780  ->
    match uu____63780 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____63839  ->
               match uu____63839 with | (y,uu____63855,uu____63856) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____63894 = as_bin_op p  in
    uu____63894 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____63951  ->
    match uu____63951 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____63979 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____63997  ->
               match uu____63997 with | (y,uu____64006) -> x = y) uu____63979
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64027 = as_uni_op p  in
    uu____64027 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64071  ->
    match uu____64071 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____64108  ->
               match uu____64108 with | (y,uu____64117) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64138 = as_standard_constructor p  in
    uu____64138 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____64188  ->
    fun inner  ->
      fun doc1  ->
        match uu____64188 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____64254 = _inner  in
              match uu____64254 with
              | (pi,fi) ->
                  let uu____64265 = _outer  in
                  (match uu____64265 with
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
                           | (uu____64283,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____64285,uu____64286) -> false)))
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
    fun uu___543_64325  ->
      if uu___543_64325 = 92
      then "\\\\"
      else
        if uu___543_64325 = 32
        then " "
        else
          if uu___543_64325 = 8
          then "\\b"
          else
            if uu___543_64325 = 9
            then "\\t"
            else
              if uu___543_64325 = 13
              then "\\r"
              else
                if uu___543_64325 = 10
                then "\\n"
                else
                  if uu___543_64325 = 39
                  then "\\'"
                  else
                    if uu___543_64325 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_64325
                      then FStar_Util.string_of_char uu___543_64325
                      else
                        if FStar_Util.is_punctuation uu___543_64325
                        then FStar_Util.string_of_char uu___543_64325
                        else
                          if FStar_Util.is_symbol uu___543_64325
                          then FStar_Util.string_of_char uu___543_64325
                          else fallback uu___543_64325
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____64372 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____64372
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
        (s,FStar_Pervasives_Native.Some (uu____64436,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64450,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____64482 =
          let uu____64484 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____64484 "\""  in
        Prims.op_Hat "\"" uu____64482
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____64490 =
          let uu____64492 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____64492 "\""  in
        Prims.op_Hat "\"" uu____64490
    | uu____64496 ->
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
              let uu____64555 =
                let uu____64556 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____64556  in
              FStar_Format.parens uu____64555  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____64566 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____64572 =
                    let uu____64573 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____64573  in
                  FStar_Format.parens uu____64572
               in
            let name1 = ptsym currentModule name  in
            let uu____64577 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____64577
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____64579,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____64583 =
              let uu____64584 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____64584  in
            maybe_paren outer t_prio_fun uu____64583
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____64586 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64586
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
        let uu____64598 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____64598

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
            let uu____64691 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64691
            then
              let uu____64694 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____64694
            else
              (let uu____64698 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____64698)
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
            let uu____64712 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____64712
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____64714 = string_of_mlconstant c  in
            FStar_Format.text uu____64714
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____64719 = ptsym currentModule path  in
            FStar_Format.text uu____64719
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____64753 =
              match uu____64753 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____64764 =
                    let uu____64767 =
                      let uu____64768 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____64768  in
                    [uu____64767; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____64764
               in
            let uu____64775 =
              let uu____64776 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____64776  in
            FStar_Format.cbrackets uu____64775
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____64790 = is_standard_constructor ctor  in
              if uu____64790
              then
                let uu____64794 =
                  let uu____64801 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64801  in
                FStar_Pervasives_Native.snd uu____64794
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____64828 = is_standard_constructor ctor  in
              if uu____64828
              then
                let uu____64832 =
                  let uu____64839 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64839  in
                FStar_Pervasives_Native.snd uu____64832
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
              | (uu____64872,uu____64873) ->
                  let uu____64880 =
                    let uu____64883 =
                      let uu____64886 =
                        let uu____64887 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____64887  in
                      [uu____64886]  in
                    (FStar_Format.text name) :: uu____64883  in
                  FStar_Format.reduce1 uu____64880
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____64898 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____64898) es
               in
            let docs1 =
              let uu____64900 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____64900  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____64917 =
                  let uu____64920 =
                    let uu____64923 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____64923]  in
                  FStar_Format.hardline :: uu____64920  in
                FStar_Format.reduce uu____64917
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____64932 =
              let uu____64933 =
                let uu____64936 =
                  let uu____64939 =
                    let uu____64942 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____64942]  in
                  doc1 :: uu____64939  in
                pre :: uu____64936  in
              FStar_Format.combine FStar_Format.hardline uu____64933  in
            FStar_Format.parens uu____64932
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____64953::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____64955;
                    FStar_Extraction_ML_Syntax.loc = uu____64956;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____64958)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____64960;
                  FStar_Extraction_ML_Syntax.loc = uu____64961;_}::[])
                 when
                 let uu____65005 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____65005 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____65031;
                            FStar_Extraction_ML_Syntax.loc = uu____65032;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____65034;
                       FStar_Extraction_ML_Syntax.loc = uu____65035;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65093;
                   FStar_Extraction_ML_Syntax.loc = uu____65094;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65107;
                   FStar_Extraction_ML_Syntax.loc = uu____65108;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____65115 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____65126 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____65126)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____65131 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65131
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____65141 =
                   let uu____65144 =
                     let uu____65147 =
                       let uu____65150 =
                         let uu____65151 = ptsym currentModule f  in
                         FStar_Format.text uu____65151  in
                       [uu____65150]  in
                     (FStar_Format.text ".") :: uu____65147  in
                   e2 :: uu____65144  in
                 FStar_Format.reduce uu____65141)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____65187 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65187
              then
                let uu____65190 =
                  let uu____65193 =
                    let uu____65196 =
                      let uu____65199 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____65201 =
                              let uu____65204 =
                                let uu____65207 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____65207]  in
                              (FStar_Format.text " : ") :: uu____65204  in
                            FStar_Format.reduce1 uu____65201
                        | uu____65209 -> FStar_Format.text ""  in
                      [uu____65199; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____65196  in
                  (FStar_Format.text "(") :: uu____65193  in
                FStar_Format.reduce1 uu____65190
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____65228  ->
                   match uu____65228 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____65240 =
                let uu____65243 =
                  let uu____65246 = FStar_Format.reduce1 ids1  in
                  [uu____65246; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____65243  in
              FStar_Format.reduce1 uu____65240  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65255 =
                let uu____65258 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65262 =
                  let uu____65265 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____65265; FStar_Format.text "end"]  in
                uu____65258 :: uu____65262  in
              FStar_Format.combine FStar_Format.hardline uu____65255  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65274 =
                let uu____65277 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65281 =
                  let uu____65284 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____65285 =
                    let uu____65288 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____65292 =
                      let uu____65295 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____65295; FStar_Format.text "end"]  in
                    uu____65288 :: uu____65292  in
                  uu____65284 :: uu____65285  in
                uu____65277 :: uu____65281  in
              FStar_Format.combine FStar_Format.hardline uu____65274  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____65334 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____65334 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____65341 =
              let uu____65344 =
                let uu____65347 =
                  let uu____65348 = ptctor currentModule exn  in
                  FStar_Format.text uu____65348  in
                [uu____65347]  in
              (FStar_Format.text "raise") :: uu____65344  in
            FStar_Format.reduce1 uu____65341
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____65360 =
              let uu____65363 =
                let uu____65366 =
                  let uu____65367 = ptctor currentModule exn  in
                  FStar_Format.text uu____65367  in
                let uu____65369 =
                  let uu____65372 =
                    let uu____65373 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____65373  in
                  [uu____65372]  in
                uu____65366 :: uu____65369  in
              (FStar_Format.text "raise") :: uu____65363  in
            FStar_Format.reduce1 uu____65360
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____65398 =
              let uu____65401 =
                let uu____65404 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____65405 =
                  let uu____65408 =
                    let uu____65411 =
                      let uu____65412 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____65412
                       in
                    [uu____65411]  in
                  (FStar_Format.text "with") :: uu____65408  in
                uu____65404 :: uu____65405  in
              (FStar_Format.text "try") :: uu____65401  in
            FStar_Format.combine FStar_Format.hardline uu____65398
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
          let uu____65436 =
            let uu____65450 = as_bin_op p  in FStar_Option.get uu____65450
             in
          match uu____65436 with
          | (uu____65479,prio,txt) ->
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
        let uu____65503 =
          let uu____65510 = as_uni_op p  in FStar_Option.get uu____65510  in
        match uu____65503 with
        | (uu____65525,txt) ->
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
          let uu____65538 = string_of_mlconstant c  in
          FStar_Format.text uu____65538
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____65574 =
            match uu____65574 with
            | (name,p) ->
                let uu____65584 =
                  let uu____65587 =
                    let uu____65588 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____65588  in
                  let uu____65594 =
                    let uu____65597 =
                      let uu____65600 = doc_of_pattern currentModule p  in
                      [uu____65600]  in
                    (FStar_Format.text "=") :: uu____65597  in
                  uu____65587 :: uu____65594  in
                FStar_Format.reduce1 uu____65584
             in
          let uu____65602 =
            let uu____65603 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____65603  in
          FStar_Format.cbrackets uu____65602
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____65617 = is_standard_constructor ctor  in
            if uu____65617
            then
              let uu____65621 =
                let uu____65628 = as_standard_constructor ctor  in
                FStar_Option.get uu____65628  in
              FStar_Pervasives_Native.snd uu____65621
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____65655 = is_standard_constructor ctor  in
            if uu____65655
            then
              let uu____65659 =
                let uu____65666 = as_standard_constructor ctor  in
                FStar_Option.get uu____65666  in
              FStar_Pervasives_Native.snd uu____65659
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____65695 =
                  let uu____65698 =
                    let uu____65699 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____65699  in
                  let uu____65700 =
                    let uu____65703 =
                      let uu____65706 = doc_of_pattern currentModule xs  in
                      [uu____65706]  in
                    (FStar_Format.text "::") :: uu____65703  in
                  uu____65698 :: uu____65700  in
                FStar_Format.reduce uu____65695
            | (uu____65708,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____65709)::[]) ->
                let uu____65716 =
                  let uu____65719 =
                    let uu____65722 =
                      let uu____65723 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____65723  in
                    [uu____65722]  in
                  (FStar_Format.text name) :: uu____65719  in
                FStar_Format.reduce1 uu____65716
            | uu____65724 ->
                let uu____65732 =
                  let uu____65735 =
                    let uu____65738 =
                      let uu____65739 =
                        let uu____65740 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____65740
                         in
                      FStar_Format.parens uu____65739  in
                    [uu____65738]  in
                  (FStar_Format.text name) :: uu____65735  in
                FStar_Format.reduce1 uu____65732
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____65755 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____65755
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65768  ->
      match uu____65768 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____65778 =
                  let uu____65781 =
                    let uu____65784 = doc_of_pattern currentModule p  in
                    [uu____65784]  in
                  (FStar_Format.text "|") :: uu____65781  in
                FStar_Format.reduce1 uu____65778
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____65788 =
                  let uu____65791 =
                    let uu____65794 = doc_of_pattern currentModule p  in
                    [uu____65794; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____65791  in
                FStar_Format.reduce1 uu____65788
             in
          let uu____65797 =
            let uu____65800 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____65803 =
              let uu____65806 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____65806; FStar_Format.text "end"]  in
            uu____65800 :: uu____65803  in
          FStar_Format.combine FStar_Format.hardline uu____65797

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65809  ->
      match uu____65809 with
      | (rec_,top_level,lets) ->
          let for1 uu____65834 =
            match uu____65834 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____65837;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____65839;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____65855 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____65855
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____65858::uu____65859,uu____65860) ->
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
                                let uu____65884 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____65884
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____65903 =
                  let uu____65906 =
                    let uu____65909 = FStar_Format.reduce1 ids  in
                    [uu____65909; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____65906  in
                FStar_Format.reduce1 uu____65903
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
  fun uu____65935  ->
    match uu____65935 with
    | (lineno,file) ->
        let uu____65942 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____65942
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
      let for1 uu____65994 =
        match uu____65994 with
        | (uu____66017,x,mangle_opt,tparams,uu____66021,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____66056 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____66067 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____66067
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____66094 =
                    match uu____66094 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____66107 =
                    let uu____66108 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____66108
                     in
                  FStar_Format.cbrackets uu____66107
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____66149 =
                    match uu____66149 with
                    | (name,tys) ->
                        let uu____66180 = FStar_List.split tys  in
                        (match uu____66180 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____66203 ->
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
              let uu____66234 =
                let uu____66237 =
                  let uu____66240 =
                    let uu____66241 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____66241  in
                  [uu____66240]  in
                tparams1 :: uu____66237  in
              FStar_Format.reduce1 uu____66234  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____66250 =
                   let uu____66253 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____66253; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____66250)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____66261 =
            let uu____66264 =
              let uu____66267 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____66267]  in
            (FStar_Format.text "type") :: uu____66264  in
          FStar_Format.reduce1 uu____66261
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
          let uu____66303 =
            let uu____66306 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____66309 =
              let uu____66312 = doc_of_sig currentModule subsig  in
              let uu____66313 =
                let uu____66316 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____66316]  in
              uu____66312 :: uu____66313  in
            uu____66306 :: uu____66309  in
          FStar_Format.combine FStar_Format.hardline uu____66303
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____66336 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____66336  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____66341,ty)) ->
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
            let uu____66420 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____66420  in
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
          let uu____66436 =
            let uu____66439 =
              let uu____66442 =
                let uu____66445 =
                  let uu____66448 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____66448]  in
                (FStar_Format.text "=") :: uu____66445  in
              (FStar_Format.text "_") :: uu____66442  in
            (FStar_Format.text "let") :: uu____66439  in
          FStar_Format.reduce1 uu____66436
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____66478 ->
                  FStar_Format.empty
              | uu____66479 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____66492  ->
    match uu____66492 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____66562 =
          match uu____66562 with
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
                  (fun uu____66622  ->
                     match uu____66622 with
                     | (s,uu____66628) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____66649 =
                let uu____66652 =
                  let uu____66655 =
                    let uu____66658 = FStar_Format.reduce sub3  in
                    [uu____66658;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____66655
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____66652
                 in
              FStar_Format.reduce uu____66649
        
        and for1_mod istop uu____66661 =
          match uu____66661 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____66743 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____66764 =
                  let uu____66767 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____66767
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
                FStar_Format.reduce1 uu____66764  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66798  ->
                     match uu____66798 with
                     | (uu____66803,m) -> doc_of_mod target_mod_name m)
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
                let uu____66829 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____66829
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____66837 =
                let uu____66840 =
                  let uu____66843 =
                    let uu____66846 =
                      let uu____66849 =
                        let uu____66852 =
                          let uu____66855 = FStar_Format.reduce sub3  in
                          [uu____66855;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____66852
                         in
                      FStar_Format.hardline :: uu____66849  in
                    FStar_List.append maybe_open_pervasives uu____66846  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____66843
                   in
                FStar_List.append prefix1 uu____66840  in
              FStar_All.pipe_left FStar_Format.reduce uu____66837
         in
        let docs =
          FStar_List.map
            (fun uu____66899  ->
               match uu____66899 with
               | (x,s,m) ->
                   let uu____66956 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____66958 = for1_mod true (x, s, m)  in
                   (uu____66956, uu____66958)) mllib
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
        let uu____67001 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____67001 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67017 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____67017 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  