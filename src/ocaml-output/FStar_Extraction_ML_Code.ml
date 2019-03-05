open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____62726 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____62737 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____62748 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____62759 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____62770 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____62786 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____62797 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____62809 -> false
  
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
    | ([],uu____63007) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____63031,uu____63032) -> false
  
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
                  let uu____63117 = FStar_Util.first_N cg_len ns  in
                  match uu____63117 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____63161 =
                           let uu____63165 =
                             let uu____63169 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____63169]  in
                           FStar_List.append pfx uu____63165  in
                         FStar_Pervasives_Native.Some uu____63161
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
      let uu____63215 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____63215 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____63231 ->
          let uu____63233 = x  in
          (match uu____63233 with
           | (ns,x1) ->
               let uu____63244 = path_of_ns currentModule ns  in
               (uu____63244, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____63262 =
      let uu____63264 =
        let uu____63266 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____63266  in
      let uu____63269 = FStar_String.get s (Prims.parse_int "0")  in
      uu____63264 <> uu____63269  in
    if uu____63262 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____63305 = mlpath_of_mlpath currentModule mlp  in
         match uu____63305 with
         | (p,s) ->
             let uu____63317 =
               let uu____63321 =
                 let uu____63325 = ptsym_of_symbol s  in [uu____63325]  in
               FStar_List.append p uu____63321  in
             FStar_String.concat "." uu____63317)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____63346 = mlpath_of_mlpath currentModule mlp  in
      match uu____63346 with
      | (p,s) ->
          let s1 =
            let uu____63360 =
              let uu____63362 =
                let uu____63364 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____63364  in
              let uu____63367 = FStar_String.get s (Prims.parse_int "0")  in
              uu____63362 <> uu____63367  in
            if uu____63360 then Prims.op_Hat "U__" s else s  in
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
  fun uu____63730  ->
    let op_minus =
      let uu____63733 =
        let uu____63735 = FStar_Options.codegen ()  in
        uu____63735 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____63733 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____63784 . unit -> 'Auu____63784 Prims.list =
  fun uu____63787  -> [] 
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
  fun uu____63882  ->
    match uu____63882 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____63941  ->
               match uu____63941 with | (y,uu____63957,uu____63958) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____63996 = as_bin_op p  in
    uu____63996 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64053  ->
    match uu____64053 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____64081 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____64099  ->
               match uu____64099 with | (y,uu____64108) -> x = y) uu____64081
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64129 = as_uni_op p  in
    uu____64129 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64173  ->
    match uu____64173 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____64210  ->
               match uu____64210 with | (y,uu____64219) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64240 = as_standard_constructor p  in
    uu____64240 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____64290  ->
    fun inner  ->
      fun doc1  ->
        match uu____64290 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____64356 = _inner  in
              match uu____64356 with
              | (pi,fi) ->
                  let uu____64367 = _outer  in
                  (match uu____64367 with
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
                           | (uu____64385,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____64387,uu____64388) -> false)))
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
    fun uu___543_64427  ->
      if uu___543_64427 = 92
      then "\\\\"
      else
        if uu___543_64427 = 32
        then " "
        else
          if uu___543_64427 = 8
          then "\\b"
          else
            if uu___543_64427 = 9
            then "\\t"
            else
              if uu___543_64427 = 13
              then "\\r"
              else
                if uu___543_64427 = 10
                then "\\n"
                else
                  if uu___543_64427 = 39
                  then "\\'"
                  else
                    if uu___543_64427 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_64427
                      then FStar_Util.string_of_char uu___543_64427
                      else
                        if FStar_Util.is_punctuation uu___543_64427
                        then FStar_Util.string_of_char uu___543_64427
                        else
                          if FStar_Util.is_symbol uu___543_64427
                          then FStar_Util.string_of_char uu___543_64427
                          else fallback uu___543_64427
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____64474 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____64474
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
        (s,FStar_Pervasives_Native.Some (uu____64538,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64552,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____64584 =
          let uu____64586 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____64586 "\""  in
        Prims.op_Hat "\"" uu____64584
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____64592 =
          let uu____64594 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____64594 "\""  in
        Prims.op_Hat "\"" uu____64592
    | uu____64598 ->
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
              let uu____64657 =
                let uu____64658 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____64658  in
              FStar_Format.parens uu____64657  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____64668 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____64674 =
                    let uu____64675 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____64675  in
                  FStar_Format.parens uu____64674
               in
            let name1 = ptsym currentModule name  in
            let uu____64679 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____64679
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____64681,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____64685 =
              let uu____64686 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____64686  in
            maybe_paren outer t_prio_fun uu____64685
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____64688 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64688
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
        let uu____64700 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____64700

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
            let uu____64793 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64793
            then
              let uu____64796 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____64796
            else
              (let uu____64800 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____64800)
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
            let uu____64814 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____64814
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____64816 = string_of_mlconstant c  in
            FStar_Format.text uu____64816
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____64821 = ptsym currentModule path  in
            FStar_Format.text uu____64821
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____64855 =
              match uu____64855 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____64866 =
                    let uu____64869 =
                      let uu____64870 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____64870  in
                    [uu____64869; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____64866
               in
            let uu____64877 =
              let uu____64878 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____64878  in
            FStar_Format.cbrackets uu____64877
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____64892 = is_standard_constructor ctor  in
              if uu____64892
              then
                let uu____64896 =
                  let uu____64903 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64903  in
                FStar_Pervasives_Native.snd uu____64896
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____64930 = is_standard_constructor ctor  in
              if uu____64930
              then
                let uu____64934 =
                  let uu____64941 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64941  in
                FStar_Pervasives_Native.snd uu____64934
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
              | (uu____64974,uu____64975) ->
                  let uu____64982 =
                    let uu____64985 =
                      let uu____64988 =
                        let uu____64989 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____64989  in
                      [uu____64988]  in
                    (FStar_Format.text name) :: uu____64985  in
                  FStar_Format.reduce1 uu____64982
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____65000 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____65000) es
               in
            let docs1 =
              let uu____65002 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____65002  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____65019 =
                  let uu____65022 =
                    let uu____65025 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____65025]  in
                  FStar_Format.hardline :: uu____65022  in
                FStar_Format.reduce uu____65019
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____65034 =
              let uu____65035 =
                let uu____65038 =
                  let uu____65041 =
                    let uu____65044 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____65044]  in
                  doc1 :: uu____65041  in
                pre :: uu____65038  in
              FStar_Format.combine FStar_Format.hardline uu____65035  in
            FStar_Format.parens uu____65034
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____65055::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____65057;
                    FStar_Extraction_ML_Syntax.loc = uu____65058;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____65060)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____65062;
                  FStar_Extraction_ML_Syntax.loc = uu____65063;_}::[])
                 when
                 let uu____65107 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____65107 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____65133;
                            FStar_Extraction_ML_Syntax.loc = uu____65134;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____65136;
                       FStar_Extraction_ML_Syntax.loc = uu____65137;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65195;
                   FStar_Extraction_ML_Syntax.loc = uu____65196;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65209;
                   FStar_Extraction_ML_Syntax.loc = uu____65210;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____65217 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____65228 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____65228)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____65233 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65233
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____65243 =
                   let uu____65246 =
                     let uu____65249 =
                       let uu____65252 =
                         let uu____65253 = ptsym currentModule f  in
                         FStar_Format.text uu____65253  in
                       [uu____65252]  in
                     (FStar_Format.text ".") :: uu____65249  in
                   e2 :: uu____65246  in
                 FStar_Format.reduce uu____65243)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____65289 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65289
              then
                let uu____65292 =
                  let uu____65295 =
                    let uu____65298 =
                      let uu____65301 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____65303 =
                              let uu____65306 =
                                let uu____65309 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____65309]  in
                              (FStar_Format.text " : ") :: uu____65306  in
                            FStar_Format.reduce1 uu____65303
                        | uu____65311 -> FStar_Format.text ""  in
                      [uu____65301; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____65298  in
                  (FStar_Format.text "(") :: uu____65295  in
                FStar_Format.reduce1 uu____65292
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____65330  ->
                   match uu____65330 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____65342 =
                let uu____65345 =
                  let uu____65348 = FStar_Format.reduce1 ids1  in
                  [uu____65348; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____65345  in
              FStar_Format.reduce1 uu____65342  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65357 =
                let uu____65360 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65364 =
                  let uu____65367 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____65367; FStar_Format.text "end"]  in
                uu____65360 :: uu____65364  in
              FStar_Format.combine FStar_Format.hardline uu____65357  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65376 =
                let uu____65379 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65383 =
                  let uu____65386 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____65387 =
                    let uu____65390 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____65394 =
                      let uu____65397 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____65397; FStar_Format.text "end"]  in
                    uu____65390 :: uu____65394  in
                  uu____65386 :: uu____65387  in
                uu____65379 :: uu____65383  in
              FStar_Format.combine FStar_Format.hardline uu____65376  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____65436 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____65436 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____65443 =
              let uu____65446 =
                let uu____65449 =
                  let uu____65450 = ptctor currentModule exn  in
                  FStar_Format.text uu____65450  in
                [uu____65449]  in
              (FStar_Format.text "raise") :: uu____65446  in
            FStar_Format.reduce1 uu____65443
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____65462 =
              let uu____65465 =
                let uu____65468 =
                  let uu____65469 = ptctor currentModule exn  in
                  FStar_Format.text uu____65469  in
                let uu____65471 =
                  let uu____65474 =
                    let uu____65475 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____65475  in
                  [uu____65474]  in
                uu____65468 :: uu____65471  in
              (FStar_Format.text "raise") :: uu____65465  in
            FStar_Format.reduce1 uu____65462
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____65500 =
              let uu____65503 =
                let uu____65506 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____65507 =
                  let uu____65510 =
                    let uu____65513 =
                      let uu____65514 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____65514
                       in
                    [uu____65513]  in
                  (FStar_Format.text "with") :: uu____65510  in
                uu____65506 :: uu____65507  in
              (FStar_Format.text "try") :: uu____65503  in
            FStar_Format.combine FStar_Format.hardline uu____65500
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
          let uu____65538 =
            let uu____65552 = as_bin_op p  in FStar_Option.get uu____65552
             in
          match uu____65538 with
          | (uu____65581,prio,txt) ->
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
        let uu____65605 =
          let uu____65612 = as_uni_op p  in FStar_Option.get uu____65612  in
        match uu____65605 with
        | (uu____65627,txt) ->
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
          let uu____65640 = string_of_mlconstant c  in
          FStar_Format.text uu____65640
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____65676 =
            match uu____65676 with
            | (name,p) ->
                let uu____65686 =
                  let uu____65689 =
                    let uu____65690 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____65690  in
                  let uu____65696 =
                    let uu____65699 =
                      let uu____65702 = doc_of_pattern currentModule p  in
                      [uu____65702]  in
                    (FStar_Format.text "=") :: uu____65699  in
                  uu____65689 :: uu____65696  in
                FStar_Format.reduce1 uu____65686
             in
          let uu____65704 =
            let uu____65705 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____65705  in
          FStar_Format.cbrackets uu____65704
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____65719 = is_standard_constructor ctor  in
            if uu____65719
            then
              let uu____65723 =
                let uu____65730 = as_standard_constructor ctor  in
                FStar_Option.get uu____65730  in
              FStar_Pervasives_Native.snd uu____65723
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____65757 = is_standard_constructor ctor  in
            if uu____65757
            then
              let uu____65761 =
                let uu____65768 = as_standard_constructor ctor  in
                FStar_Option.get uu____65768  in
              FStar_Pervasives_Native.snd uu____65761
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____65797 =
                  let uu____65800 =
                    let uu____65801 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____65801  in
                  let uu____65802 =
                    let uu____65805 =
                      let uu____65808 = doc_of_pattern currentModule xs  in
                      [uu____65808]  in
                    (FStar_Format.text "::") :: uu____65805  in
                  uu____65800 :: uu____65802  in
                FStar_Format.reduce uu____65797
            | (uu____65810,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____65811)::[]) ->
                let uu____65818 =
                  let uu____65821 =
                    let uu____65824 =
                      let uu____65825 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____65825  in
                    [uu____65824]  in
                  (FStar_Format.text name) :: uu____65821  in
                FStar_Format.reduce1 uu____65818
            | uu____65826 ->
                let uu____65834 =
                  let uu____65837 =
                    let uu____65840 =
                      let uu____65841 =
                        let uu____65842 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____65842
                         in
                      FStar_Format.parens uu____65841  in
                    [uu____65840]  in
                  (FStar_Format.text name) :: uu____65837  in
                FStar_Format.reduce1 uu____65834
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____65857 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____65857
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65870  ->
      match uu____65870 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____65880 =
                  let uu____65883 =
                    let uu____65886 = doc_of_pattern currentModule p  in
                    [uu____65886]  in
                  (FStar_Format.text "|") :: uu____65883  in
                FStar_Format.reduce1 uu____65880
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____65890 =
                  let uu____65893 =
                    let uu____65896 = doc_of_pattern currentModule p  in
                    [uu____65896; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____65893  in
                FStar_Format.reduce1 uu____65890
             in
          let uu____65899 =
            let uu____65902 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____65905 =
              let uu____65908 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____65908; FStar_Format.text "end"]  in
            uu____65902 :: uu____65905  in
          FStar_Format.combine FStar_Format.hardline uu____65899

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65911  ->
      match uu____65911 with
      | (rec_,top_level,lets) ->
          let for1 uu____65936 =
            match uu____65936 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____65939;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____65941;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____65957 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____65957
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____65960::uu____65961,uu____65962) ->
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
                                let uu____65986 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____65986
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____66005 =
                  let uu____66008 =
                    let uu____66011 = FStar_Format.reduce1 ids  in
                    [uu____66011; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____66008  in
                FStar_Format.reduce1 uu____66005
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
  fun uu____66037  ->
    match uu____66037 with
    | (lineno,file) ->
        let uu____66044 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____66044
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
      let for1 uu____66096 =
        match uu____66096 with
        | (uu____66119,x,mangle_opt,tparams,uu____66123,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____66158 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____66169 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____66169
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____66196 =
                    match uu____66196 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____66209 =
                    let uu____66210 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____66210
                     in
                  FStar_Format.cbrackets uu____66209
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____66251 =
                    match uu____66251 with
                    | (name,tys) ->
                        let uu____66282 = FStar_List.split tys  in
                        (match uu____66282 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____66305 ->
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
              let uu____66336 =
                let uu____66339 =
                  let uu____66342 =
                    let uu____66343 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____66343  in
                  [uu____66342]  in
                tparams1 :: uu____66339  in
              FStar_Format.reduce1 uu____66336  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____66352 =
                   let uu____66355 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____66355; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____66352)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____66363 =
            let uu____66366 =
              let uu____66369 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____66369]  in
            (FStar_Format.text "type") :: uu____66366  in
          FStar_Format.reduce1 uu____66363
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
          let uu____66405 =
            let uu____66408 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____66411 =
              let uu____66414 = doc_of_sig currentModule subsig  in
              let uu____66415 =
                let uu____66418 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____66418]  in
              uu____66414 :: uu____66415  in
            uu____66408 :: uu____66411  in
          FStar_Format.combine FStar_Format.hardline uu____66405
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____66438 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____66438  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____66443,ty)) ->
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
            let uu____66522 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____66522  in
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
          let uu____66538 =
            let uu____66541 =
              let uu____66544 =
                let uu____66547 =
                  let uu____66550 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____66550]  in
                (FStar_Format.text "=") :: uu____66547  in
              (FStar_Format.text "_") :: uu____66544  in
            (FStar_Format.text "let") :: uu____66541  in
          FStar_Format.reduce1 uu____66538
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____66580 ->
                  FStar_Format.empty
              | uu____66581 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____66594  ->
    match uu____66594 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____66664 =
          match uu____66664 with
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
                  (fun uu____66724  ->
                     match uu____66724 with
                     | (s,uu____66730) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____66751 =
                let uu____66754 =
                  let uu____66757 =
                    let uu____66760 = FStar_Format.reduce sub3  in
                    [uu____66760;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____66757
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____66754
                 in
              FStar_Format.reduce uu____66751
        
        and for1_mod istop uu____66763 =
          match uu____66763 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____66845 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____66866 =
                  let uu____66869 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____66869
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
                FStar_Format.reduce1 uu____66866  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66900  ->
                     match uu____66900 with
                     | (uu____66905,m) -> doc_of_mod target_mod_name m)
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
                let uu____66931 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____66931
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____66939 =
                let uu____66942 =
                  let uu____66945 =
                    let uu____66948 =
                      let uu____66951 =
                        let uu____66954 =
                          let uu____66957 = FStar_Format.reduce sub3  in
                          [uu____66957;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____66954
                         in
                      FStar_Format.hardline :: uu____66951  in
                    FStar_List.append maybe_open_pervasives uu____66948  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____66945
                   in
                FStar_List.append prefix1 uu____66942  in
              FStar_All.pipe_left FStar_Format.reduce uu____66939
         in
        let docs =
          FStar_List.map
            (fun uu____67001  ->
               match uu____67001 with
               | (x,s,m) ->
                   let uu____67058 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____67060 = for1_mod true (x, s, m)  in
                   (uu____67058, uu____67060)) mllib
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
        let uu____67103 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____67103 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67119 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____67119 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  