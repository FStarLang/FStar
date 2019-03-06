open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____58779 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____58790 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____58801 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____58812 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____58823 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____58839 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____58850 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____58862 -> false
  
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
    | ([],uu____59060) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____59084,uu____59085) -> false
  
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
                  let uu____59166 = FStar_Util.first_N cg_len ns  in
                  match uu____59166 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____59206 =
                           let uu____59210 =
                             let uu____59214 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____59214]  in
                           FStar_List.append pfx uu____59210  in
                         FStar_Pervasives_Native.Some uu____59206
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
      let uu____59260 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____59260 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____59276 ->
          let uu____59278 = x  in
          (match uu____59278 with
           | (ns,x1) ->
               let uu____59289 = path_of_ns currentModule ns  in
               (uu____59289, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____59307 =
      let uu____59309 =
        let uu____59311 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____59311  in
      let uu____59314 = FStar_String.get s (Prims.parse_int "0")  in
      uu____59309 <> uu____59314  in
    if uu____59307 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____59350 = mlpath_of_mlpath currentModule mlp  in
         match uu____59350 with
         | (p,s) ->
             let uu____59362 =
               let uu____59366 =
                 let uu____59370 = ptsym_of_symbol s  in [uu____59370]  in
               FStar_List.append p uu____59366  in
             FStar_String.concat "." uu____59362)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____59391 = mlpath_of_mlpath currentModule mlp  in
      match uu____59391 with
      | (p,s) ->
          let s1 =
            let uu____59405 =
              let uu____59407 =
                let uu____59409 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____59409  in
              let uu____59412 = FStar_String.get s (Prims.parse_int "0")  in
              uu____59407 <> uu____59412  in
            if uu____59405 then Prims.op_Hat "U__" s else s  in
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
  fun uu____59775  ->
    let op_minus =
      let uu____59778 =
        let uu____59780 = FStar_Options.codegen ()  in
        uu____59780 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____59778 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____59829 . unit -> 'Auu____59829 Prims.list =
  fun uu____59832  -> [] 
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
  fun uu____59927  ->
    match uu____59927 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59986  ->
               match uu____59986 with | (y,uu____60002,uu____60003) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____60041 = as_bin_op p  in
    uu____60041 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____60098  ->
    match uu____60098 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____60126 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____60144  ->
               match uu____60144 with | (y,uu____60153) -> x = y) uu____60126
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____60174 = as_uni_op p  in
    uu____60174 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____60218  ->
    match uu____60218 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____60255  ->
               match uu____60255 with | (y,uu____60264) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____60285 = as_standard_constructor p  in
    uu____60285 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____60335  ->
    fun inner  ->
      fun doc1  ->
        match uu____60335 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____60401 = _inner  in
              match uu____60401 with
              | (pi,fi) ->
                  let uu____60412 = _outer  in
                  (match uu____60412 with
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
                           | (uu____60430,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____60432,uu____60433) -> false)))
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
    fun uu___543_60472  ->
      if uu___543_60472 = 92
      then "\\\\"
      else
        if uu___543_60472 = 32
        then " "
        else
          if uu___543_60472 = 8
          then "\\b"
          else
            if uu___543_60472 = 9
            then "\\t"
            else
              if uu___543_60472 = 13
              then "\\r"
              else
                if uu___543_60472 = 10
                then "\\n"
                else
                  if uu___543_60472 = 39
                  then "\\'"
                  else
                    if uu___543_60472 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_60472
                      then FStar_Util.string_of_char uu___543_60472
                      else
                        if FStar_Util.is_punctuation uu___543_60472
                        then FStar_Util.string_of_char uu___543_60472
                        else
                          if FStar_Util.is_symbol uu___543_60472
                          then FStar_Util.string_of_char uu___543_60472
                          else fallback uu___543_60472
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____60519 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____60519
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
        (s,FStar_Pervasives_Native.Some (uu____60561,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____60575,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____60607 =
          let uu____60609 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____60609 "\""  in
        Prims.op_Hat "\"" uu____60607
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____60615 =
          let uu____60617 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____60617 "\""  in
        Prims.op_Hat "\"" uu____60615
    | uu____60621 ->
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
              let uu____60680 =
                let uu____60681 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____60681  in
              FStar_Format.parens uu____60680  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____60691 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____60697 =
                    let uu____60698 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____60698  in
                  FStar_Format.parens uu____60697
               in
            let name1 = ptsym currentModule name  in
            let uu____60702 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____60702
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____60704,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____60708 =
              let uu____60709 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____60709  in
            maybe_paren outer t_prio_fun uu____60708
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____60711 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60711
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
        let uu____60723 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____60723

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
            let uu____60816 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60816
            then
              let uu____60819 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____60819
            else
              (let uu____60823 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____60823)
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
            let uu____60837 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____60837
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____60839 = string_of_mlconstant c  in
            FStar_Format.text uu____60839
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____60844 = ptsym currentModule path  in
            FStar_Format.text uu____60844
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____60878 =
              match uu____60878 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60889 =
                    let uu____60892 =
                      let uu____60893 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____60893  in
                    [uu____60892; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____60889
               in
            let uu____60900 =
              let uu____60901 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____60901  in
            FStar_Format.cbrackets uu____60900
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____60915 = is_standard_constructor ctor  in
              if uu____60915
              then
                let uu____60919 =
                  let uu____60926 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60926  in
                FStar_Pervasives_Native.snd uu____60919
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____60953 = is_standard_constructor ctor  in
              if uu____60953
              then
                let uu____60957 =
                  let uu____60964 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60964  in
                FStar_Pervasives_Native.snd uu____60957
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
              | (uu____60997,uu____60998) ->
                  let uu____61005 =
                    let uu____61008 =
                      let uu____61011 =
                        let uu____61012 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____61012  in
                      [uu____61011]  in
                    (FStar_Format.text name) :: uu____61008  in
                  FStar_Format.reduce1 uu____61005
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____61023 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____61023) es
               in
            let docs1 =
              let uu____61025 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____61025  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____61042 =
                  let uu____61045 =
                    let uu____61048 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____61048]  in
                  FStar_Format.hardline :: uu____61045  in
                FStar_Format.reduce uu____61042
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____61057 =
              let uu____61058 =
                let uu____61061 =
                  let uu____61064 =
                    let uu____61067 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____61067]  in
                  doc1 :: uu____61064  in
                pre :: uu____61061  in
              FStar_Format.combine FStar_Format.hardline uu____61058  in
            FStar_Format.parens uu____61057
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____61078::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____61080;
                    FStar_Extraction_ML_Syntax.loc = uu____61081;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____61083)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____61085;
                  FStar_Extraction_ML_Syntax.loc = uu____61086;_}::[])
                 when
                 let uu____61130 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____61130 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____61156;
                            FStar_Extraction_ML_Syntax.loc = uu____61157;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____61159;
                       FStar_Extraction_ML_Syntax.loc = uu____61160;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____61218;
                   FStar_Extraction_ML_Syntax.loc = uu____61219;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____61232;
                   FStar_Extraction_ML_Syntax.loc = uu____61233;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____61240 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____61251 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____61251)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____61256 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____61256
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____61266 =
                   let uu____61269 =
                     let uu____61272 =
                       let uu____61275 =
                         let uu____61276 = ptsym currentModule f  in
                         FStar_Format.text uu____61276  in
                       [uu____61275]  in
                     (FStar_Format.text ".") :: uu____61272  in
                   e2 :: uu____61269  in
                 FStar_Format.reduce uu____61266)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____61312 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____61312
              then
                let uu____61315 =
                  let uu____61318 =
                    let uu____61321 =
                      let uu____61324 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____61326 =
                              let uu____61329 =
                                let uu____61332 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____61332]  in
                              (FStar_Format.text " : ") :: uu____61329  in
                            FStar_Format.reduce1 uu____61326
                        | uu____61334 -> FStar_Format.text ""  in
                      [uu____61324; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____61321  in
                  (FStar_Format.text "(") :: uu____61318  in
                FStar_Format.reduce1 uu____61315
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____61353  ->
                   match uu____61353 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____61365 =
                let uu____61368 =
                  let uu____61371 = FStar_Format.reduce1 ids1  in
                  [uu____61371; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____61368  in
              FStar_Format.reduce1 uu____61365  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____61380 =
                let uu____61383 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____61387 =
                  let uu____61390 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____61390; FStar_Format.text "end"]  in
                uu____61383 :: uu____61387  in
              FStar_Format.combine FStar_Format.hardline uu____61380  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____61399 =
                let uu____61402 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____61406 =
                  let uu____61409 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____61410 =
                    let uu____61413 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____61417 =
                      let uu____61420 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____61420; FStar_Format.text "end"]  in
                    uu____61413 :: uu____61417  in
                  uu____61409 :: uu____61410  in
                uu____61402 :: uu____61406  in
              FStar_Format.combine FStar_Format.hardline uu____61399  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____61459 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____61459 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____61466 =
              let uu____61469 =
                let uu____61472 =
                  let uu____61473 = ptctor currentModule exn  in
                  FStar_Format.text uu____61473  in
                [uu____61472]  in
              (FStar_Format.text "raise") :: uu____61469  in
            FStar_Format.reduce1 uu____61466
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____61485 =
              let uu____61488 =
                let uu____61491 =
                  let uu____61492 = ptctor currentModule exn  in
                  FStar_Format.text uu____61492  in
                let uu____61494 =
                  let uu____61497 =
                    let uu____61498 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____61498  in
                  [uu____61497]  in
                uu____61491 :: uu____61494  in
              (FStar_Format.text "raise") :: uu____61488  in
            FStar_Format.reduce1 uu____61485
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____61523 =
              let uu____61526 =
                let uu____61529 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____61530 =
                  let uu____61533 =
                    let uu____61536 =
                      let uu____61537 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____61537
                       in
                    [uu____61536]  in
                  (FStar_Format.text "with") :: uu____61533  in
                uu____61529 :: uu____61530  in
              (FStar_Format.text "try") :: uu____61526  in
            FStar_Format.combine FStar_Format.hardline uu____61523
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
          let uu____61561 =
            let uu____61575 = as_bin_op p  in FStar_Option.get uu____61575
             in
          match uu____61561 with
          | (uu____61604,prio,txt) ->
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
        let uu____61628 =
          let uu____61635 = as_uni_op p  in FStar_Option.get uu____61635  in
        match uu____61628 with
        | (uu____61650,txt) ->
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
          let uu____61663 = string_of_mlconstant c  in
          FStar_Format.text uu____61663
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____61699 =
            match uu____61699 with
            | (name,p) ->
                let uu____61709 =
                  let uu____61712 =
                    let uu____61713 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____61713  in
                  let uu____61719 =
                    let uu____61722 =
                      let uu____61725 = doc_of_pattern currentModule p  in
                      [uu____61725]  in
                    (FStar_Format.text "=") :: uu____61722  in
                  uu____61712 :: uu____61719  in
                FStar_Format.reduce1 uu____61709
             in
          let uu____61727 =
            let uu____61728 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____61728  in
          FStar_Format.cbrackets uu____61727
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____61742 = is_standard_constructor ctor  in
            if uu____61742
            then
              let uu____61746 =
                let uu____61753 = as_standard_constructor ctor  in
                FStar_Option.get uu____61753  in
              FStar_Pervasives_Native.snd uu____61746
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____61780 = is_standard_constructor ctor  in
            if uu____61780
            then
              let uu____61784 =
                let uu____61791 = as_standard_constructor ctor  in
                FStar_Option.get uu____61791  in
              FStar_Pervasives_Native.snd uu____61784
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____61820 =
                  let uu____61823 =
                    let uu____61824 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____61824  in
                  let uu____61825 =
                    let uu____61828 =
                      let uu____61831 = doc_of_pattern currentModule xs  in
                      [uu____61831]  in
                    (FStar_Format.text "::") :: uu____61828  in
                  uu____61823 :: uu____61825  in
                FStar_Format.reduce uu____61820
            | (uu____61833,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____61834)::[]) ->
                let uu____61841 =
                  let uu____61844 =
                    let uu____61847 =
                      let uu____61848 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____61848  in
                    [uu____61847]  in
                  (FStar_Format.text name) :: uu____61844  in
                FStar_Format.reduce1 uu____61841
            | uu____61849 ->
                let uu____61857 =
                  let uu____61860 =
                    let uu____61863 =
                      let uu____61864 =
                        let uu____61865 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____61865
                         in
                      FStar_Format.parens uu____61864  in
                    [uu____61863]  in
                  (FStar_Format.text name) :: uu____61860  in
                FStar_Format.reduce1 uu____61857
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____61880 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____61880
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61893  ->
      match uu____61893 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____61903 =
                  let uu____61906 =
                    let uu____61909 = doc_of_pattern currentModule p  in
                    [uu____61909]  in
                  (FStar_Format.text "|") :: uu____61906  in
                FStar_Format.reduce1 uu____61903
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____61913 =
                  let uu____61916 =
                    let uu____61919 = doc_of_pattern currentModule p  in
                    [uu____61919; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____61916  in
                FStar_Format.reduce1 uu____61913
             in
          let uu____61922 =
            let uu____61925 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____61928 =
              let uu____61931 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____61931; FStar_Format.text "end"]  in
            uu____61925 :: uu____61928  in
          FStar_Format.combine FStar_Format.hardline uu____61922

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61934  ->
      match uu____61934 with
      | (rec_,top_level,lets) ->
          let for1 uu____61959 =
            match uu____61959 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____61962;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____61964;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____61980 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____61980
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____61983::uu____61984,uu____61985) ->
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
                                let uu____62009 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____62009
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____62028 =
                  let uu____62031 =
                    let uu____62034 = FStar_Format.reduce1 ids  in
                    [uu____62034; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____62031  in
                FStar_Format.reduce1 uu____62028
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
  fun uu____62060  ->
    match uu____62060 with
    | (lineno,file) ->
        let uu____62067 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____62067
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
      let for1 uu____62119 =
        match uu____62119 with
        | (uu____62142,x,mangle_opt,tparams,uu____62146,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____62181 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____62192 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____62192
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____62219 =
                    match uu____62219 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____62232 =
                    let uu____62233 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____62233
                     in
                  FStar_Format.cbrackets uu____62232
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____62274 =
                    match uu____62274 with
                    | (name,tys) ->
                        let uu____62305 = FStar_List.split tys  in
                        (match uu____62305 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____62328 ->
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
              let uu____62359 =
                let uu____62362 =
                  let uu____62365 =
                    let uu____62366 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____62366  in
                  [uu____62365]  in
                tparams1 :: uu____62362  in
              FStar_Format.reduce1 uu____62359  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____62375 =
                   let uu____62378 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____62378; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____62375)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____62386 =
            let uu____62389 =
              let uu____62392 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____62392]  in
            (FStar_Format.text "type") :: uu____62389  in
          FStar_Format.reduce1 uu____62386
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
          let uu____62428 =
            let uu____62431 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____62434 =
              let uu____62437 = doc_of_sig currentModule subsig  in
              let uu____62438 =
                let uu____62441 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____62441]  in
              uu____62437 :: uu____62438  in
            uu____62431 :: uu____62434  in
          FStar_Format.combine FStar_Format.hardline uu____62428
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____62461 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____62461  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____62466,ty)) ->
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
            let uu____62545 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____62545  in
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
          let uu____62561 =
            let uu____62564 =
              let uu____62567 =
                let uu____62570 =
                  let uu____62573 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____62573]  in
                (FStar_Format.text "=") :: uu____62570  in
              (FStar_Format.text "_") :: uu____62567  in
            (FStar_Format.text "let") :: uu____62564  in
          FStar_Format.reduce1 uu____62561
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____62603 ->
                  FStar_Format.empty
              | uu____62604 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____62617  ->
    match uu____62617 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____62687 =
          match uu____62687 with
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
                  (fun uu____62747  ->
                     match uu____62747 with
                     | (s,uu____62753) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____62774 =
                let uu____62777 =
                  let uu____62780 =
                    let uu____62783 = FStar_Format.reduce sub3  in
                    [uu____62783;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____62780
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____62777
                 in
              FStar_Format.reduce uu____62774
        
        and for1_mod istop uu____62786 =
          match uu____62786 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____62868 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____62889 =
                  let uu____62892 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____62892
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
                FStar_Format.reduce1 uu____62889  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____62923  ->
                     match uu____62923 with
                     | (uu____62928,m) -> doc_of_mod target_mod_name m)
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
                let uu____62954 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____62954
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____62962 =
                let uu____62965 =
                  let uu____62968 =
                    let uu____62971 =
                      let uu____62974 =
                        let uu____62977 =
                          let uu____62980 = FStar_Format.reduce sub3  in
                          [uu____62980;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____62977
                         in
                      FStar_Format.hardline :: uu____62974  in
                    FStar_List.append maybe_open_pervasives uu____62971  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____62968
                   in
                FStar_List.append prefix1 uu____62965  in
              FStar_All.pipe_left FStar_Format.reduce uu____62962
         in
        let docs =
          FStar_List.map
            (fun uu____63024  ->
               match uu____63024 with
               | (x,s,m) ->
                   let uu____63081 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____63083 = for1_mod true (x, s, m)  in
                   (uu____63081, uu____63083)) mllib
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
        let uu____63126 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____63126 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____63142 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____63142 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  