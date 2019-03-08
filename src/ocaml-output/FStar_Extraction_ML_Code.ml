open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____57986 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____57997 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____58008 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____58019 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____58030 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____58046 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____58057 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____58069 -> false
  
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
    | ([],uu____58266) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____58290,uu____58291) -> false
  
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
                  let uu____58372 = FStar_Util.first_N cg_len ns  in
                  match uu____58372 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____58412 =
                           let uu____58416 =
                             let uu____58420 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____58420]  in
                           FStar_List.append pfx uu____58416  in
                         FStar_Pervasives_Native.Some uu____58412
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
      let uu____58466 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____58466 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____58482 ->
          let uu____58484 = x  in
          (match uu____58484 with
           | (ns,x1) ->
               let uu____58495 = path_of_ns currentModule ns  in
               (uu____58495, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____58513 =
      let uu____58515 =
        let uu____58517 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____58517  in
      let uu____58520 = FStar_String.get s (Prims.parse_int "0")  in
      uu____58515 <> uu____58520  in
    if uu____58513 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____58556 = mlpath_of_mlpath currentModule mlp  in
         match uu____58556 with
         | (p,s) ->
             let uu____58568 =
               let uu____58572 =
                 let uu____58576 = ptsym_of_symbol s  in [uu____58576]  in
               FStar_List.append p uu____58572  in
             FStar_String.concat "." uu____58568)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____58597 = mlpath_of_mlpath currentModule mlp  in
      match uu____58597 with
      | (p,s) ->
          let s1 =
            let uu____58611 =
              let uu____58613 =
                let uu____58615 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____58615  in
              let uu____58618 = FStar_String.get s (Prims.parse_int "0")  in
              uu____58613 <> uu____58618  in
            if uu____58611 then Prims.op_Hat "U__" s else s  in
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
  fun uu____58981  ->
    let op_minus =
      let uu____58984 =
        let uu____58986 = FStar_Options.codegen ()  in
        uu____58986 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____58984 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____59035 . unit -> 'Auu____59035 Prims.list =
  fun uu____59038  -> [] 
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
  fun uu____59133  ->
    match uu____59133 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59192  ->
               match uu____59192 with | (y,uu____59208,uu____59209) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59247 = as_bin_op p  in
    uu____59247 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59304  ->
    match uu____59304 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____59332 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____59350  ->
               match uu____59350 with | (y,uu____59359) -> x = y) uu____59332
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59380 = as_uni_op p  in
    uu____59380 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59424  ->
    match uu____59424 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59461  ->
               match uu____59461 with | (y,uu____59470) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59491 = as_standard_constructor p  in
    uu____59491 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____59541  ->
    fun inner  ->
      fun doc1  ->
        match uu____59541 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____59607 = _inner  in
              match uu____59607 with
              | (pi,fi) ->
                  let uu____59618 = _outer  in
                  (match uu____59618 with
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
                           | (uu____59636,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____59638,uu____59639) -> false)))
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
    fun uu___543_59678  ->
      if uu___543_59678 = 92
      then "\\\\"
      else
        if uu___543_59678 = 32
        then " "
        else
          if uu___543_59678 = 8
          then "\\b"
          else
            if uu___543_59678 = 9
            then "\\t"
            else
              if uu___543_59678 = 13
              then "\\r"
              else
                if uu___543_59678 = 10
                then "\\n"
                else
                  if uu___543_59678 = 39
                  then "\\'"
                  else
                    if uu___543_59678 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_59678
                      then FStar_Util.string_of_char uu___543_59678
                      else
                        if FStar_Util.is_punctuation uu___543_59678
                        then FStar_Util.string_of_char uu___543_59678
                        else
                          if FStar_Util.is_symbol uu___543_59678
                          then FStar_Util.string_of_char uu___543_59678
                          else fallback uu___543_59678
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____59725 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____59725
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
        (s,FStar_Pervasives_Native.Some (uu____59767,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____59781,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____59813 =
          let uu____59815 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____59815 "\""  in
        Prims.op_Hat "\"" uu____59813
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____59821 =
          let uu____59823 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____59823 "\""  in
        Prims.op_Hat "\"" uu____59821
    | uu____59827 ->
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
              let uu____59886 =
                let uu____59887 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____59887  in
              FStar_Format.parens uu____59886  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____59897 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____59903 =
                    let uu____59904 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____59904  in
                  FStar_Format.parens uu____59903
               in
            let name1 = ptsym currentModule name  in
            let uu____59908 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____59908
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____59910,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____59914 =
              let uu____59915 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____59915  in
            maybe_paren outer t_prio_fun uu____59914
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____59917 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____59917
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
        let uu____59929 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____59929

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
            let uu____60022 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60022
            then
              let uu____60025 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____60025
            else
              (let uu____60029 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____60029)
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
            let uu____60043 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____60043
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____60045 = string_of_mlconstant c  in
            FStar_Format.text uu____60045
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____60050 = ptsym currentModule path  in
            FStar_Format.text uu____60050
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____60084 =
              match uu____60084 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60095 =
                    let uu____60098 =
                      let uu____60099 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____60099  in
                    [uu____60098; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____60095
               in
            let uu____60106 =
              let uu____60107 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____60107  in
            FStar_Format.cbrackets uu____60106
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____60121 = is_standard_constructor ctor  in
              if uu____60121
              then
                let uu____60125 =
                  let uu____60132 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60132  in
                FStar_Pervasives_Native.snd uu____60125
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____60159 = is_standard_constructor ctor  in
              if uu____60159
              then
                let uu____60163 =
                  let uu____60170 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60170  in
                FStar_Pervasives_Native.snd uu____60163
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
              | (uu____60203,uu____60204) ->
                  let uu____60211 =
                    let uu____60214 =
                      let uu____60217 =
                        let uu____60218 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____60218  in
                      [uu____60217]  in
                    (FStar_Format.text name) :: uu____60214  in
                  FStar_Format.reduce1 uu____60211
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____60229 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____60229) es
               in
            let docs1 =
              let uu____60231 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____60231  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____60248 =
                  let uu____60251 =
                    let uu____60254 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____60254]  in
                  FStar_Format.hardline :: uu____60251  in
                FStar_Format.reduce uu____60248
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____60263 =
              let uu____60264 =
                let uu____60267 =
                  let uu____60270 =
                    let uu____60273 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____60273]  in
                  doc1 :: uu____60270  in
                pre :: uu____60267  in
              FStar_Format.combine FStar_Format.hardline uu____60264  in
            FStar_Format.parens uu____60263
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____60284::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____60286;
                    FStar_Extraction_ML_Syntax.loc = uu____60287;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____60289)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____60291;
                  FStar_Extraction_ML_Syntax.loc = uu____60292;_}::[])
                 when
                 let uu____60336 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____60336 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____60362;
                            FStar_Extraction_ML_Syntax.loc = uu____60363;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____60365;
                       FStar_Extraction_ML_Syntax.loc = uu____60366;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60424;
                   FStar_Extraction_ML_Syntax.loc = uu____60425;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60438;
                   FStar_Extraction_ML_Syntax.loc = uu____60439;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____60446 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____60457 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____60457)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____60462 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60462
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____60472 =
                   let uu____60475 =
                     let uu____60478 =
                       let uu____60481 =
                         let uu____60482 = ptsym currentModule f  in
                         FStar_Format.text uu____60482  in
                       [uu____60481]  in
                     (FStar_Format.text ".") :: uu____60478  in
                   e2 :: uu____60475  in
                 FStar_Format.reduce uu____60472)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____60518 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60518
              then
                let uu____60521 =
                  let uu____60524 =
                    let uu____60527 =
                      let uu____60530 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____60532 =
                              let uu____60535 =
                                let uu____60538 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____60538]  in
                              (FStar_Format.text " : ") :: uu____60535  in
                            FStar_Format.reduce1 uu____60532
                        | uu____60540 -> FStar_Format.text ""  in
                      [uu____60530; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____60527  in
                  (FStar_Format.text "(") :: uu____60524  in
                FStar_Format.reduce1 uu____60521
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____60559  ->
                   match uu____60559 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____60571 =
                let uu____60574 =
                  let uu____60577 = FStar_Format.reduce1 ids1  in
                  [uu____60577; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____60574  in
              FStar_Format.reduce1 uu____60571  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60586 =
                let uu____60589 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60593 =
                  let uu____60596 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____60596; FStar_Format.text "end"]  in
                uu____60589 :: uu____60593  in
              FStar_Format.combine FStar_Format.hardline uu____60586  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60605 =
                let uu____60608 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60612 =
                  let uu____60615 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60616 =
                    let uu____60619 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____60623 =
                      let uu____60626 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____60626; FStar_Format.text "end"]  in
                    uu____60619 :: uu____60623  in
                  uu____60615 :: uu____60616  in
                uu____60608 :: uu____60612  in
              FStar_Format.combine FStar_Format.hardline uu____60605  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____60665 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____60665 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____60672 =
              let uu____60675 =
                let uu____60678 =
                  let uu____60679 = ptctor currentModule exn  in
                  FStar_Format.text uu____60679  in
                [uu____60678]  in
              (FStar_Format.text "raise") :: uu____60675  in
            FStar_Format.reduce1 uu____60672
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____60691 =
              let uu____60694 =
                let uu____60697 =
                  let uu____60698 = ptctor currentModule exn  in
                  FStar_Format.text uu____60698  in
                let uu____60700 =
                  let uu____60703 =
                    let uu____60704 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____60704  in
                  [uu____60703]  in
                uu____60697 :: uu____60700  in
              (FStar_Format.text "raise") :: uu____60694  in
            FStar_Format.reduce1 uu____60691
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____60729 =
              let uu____60732 =
                let uu____60735 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____60736 =
                  let uu____60739 =
                    let uu____60742 =
                      let uu____60743 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____60743
                       in
                    [uu____60742]  in
                  (FStar_Format.text "with") :: uu____60739  in
                uu____60735 :: uu____60736  in
              (FStar_Format.text "try") :: uu____60732  in
            FStar_Format.combine FStar_Format.hardline uu____60729
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
          let uu____60767 =
            let uu____60781 = as_bin_op p  in FStar_Option.get uu____60781
             in
          match uu____60767 with
          | (uu____60810,prio,txt) ->
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
        let uu____60834 =
          let uu____60841 = as_uni_op p  in FStar_Option.get uu____60841  in
        match uu____60834 with
        | (uu____60856,txt) ->
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
          let uu____60869 = string_of_mlconstant c  in
          FStar_Format.text uu____60869
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____60905 =
            match uu____60905 with
            | (name,p) ->
                let uu____60915 =
                  let uu____60918 =
                    let uu____60919 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____60919  in
                  let uu____60925 =
                    let uu____60928 =
                      let uu____60931 = doc_of_pattern currentModule p  in
                      [uu____60931]  in
                    (FStar_Format.text "=") :: uu____60928  in
                  uu____60918 :: uu____60925  in
                FStar_Format.reduce1 uu____60915
             in
          let uu____60933 =
            let uu____60934 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____60934  in
          FStar_Format.cbrackets uu____60933
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____60948 = is_standard_constructor ctor  in
            if uu____60948
            then
              let uu____60952 =
                let uu____60959 = as_standard_constructor ctor  in
                FStar_Option.get uu____60959  in
              FStar_Pervasives_Native.snd uu____60952
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____60986 = is_standard_constructor ctor  in
            if uu____60986
            then
              let uu____60990 =
                let uu____60997 = as_standard_constructor ctor  in
                FStar_Option.get uu____60997  in
              FStar_Pervasives_Native.snd uu____60990
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____61026 =
                  let uu____61029 =
                    let uu____61030 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____61030  in
                  let uu____61031 =
                    let uu____61034 =
                      let uu____61037 = doc_of_pattern currentModule xs  in
                      [uu____61037]  in
                    (FStar_Format.text "::") :: uu____61034  in
                  uu____61029 :: uu____61031  in
                FStar_Format.reduce uu____61026
            | (uu____61039,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____61040)::[]) ->
                let uu____61047 =
                  let uu____61050 =
                    let uu____61053 =
                      let uu____61054 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____61054  in
                    [uu____61053]  in
                  (FStar_Format.text name) :: uu____61050  in
                FStar_Format.reduce1 uu____61047
            | uu____61055 ->
                let uu____61063 =
                  let uu____61066 =
                    let uu____61069 =
                      let uu____61070 =
                        let uu____61071 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____61071
                         in
                      FStar_Format.parens uu____61070  in
                    [uu____61069]  in
                  (FStar_Format.text name) :: uu____61066  in
                FStar_Format.reduce1 uu____61063
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____61086 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____61086
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61099  ->
      match uu____61099 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____61109 =
                  let uu____61112 =
                    let uu____61115 = doc_of_pattern currentModule p  in
                    [uu____61115]  in
                  (FStar_Format.text "|") :: uu____61112  in
                FStar_Format.reduce1 uu____61109
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____61119 =
                  let uu____61122 =
                    let uu____61125 = doc_of_pattern currentModule p  in
                    [uu____61125; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____61122  in
                FStar_Format.reduce1 uu____61119
             in
          let uu____61128 =
            let uu____61131 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____61134 =
              let uu____61137 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____61137; FStar_Format.text "end"]  in
            uu____61131 :: uu____61134  in
          FStar_Format.combine FStar_Format.hardline uu____61128

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61140  ->
      match uu____61140 with
      | (rec_,top_level,lets) ->
          let for1 uu____61165 =
            match uu____61165 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____61168;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____61170;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____61186 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____61186
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____61189::uu____61190,uu____61191) ->
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
                                let uu____61215 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____61215
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____61234 =
                  let uu____61237 =
                    let uu____61240 = FStar_Format.reduce1 ids  in
                    [uu____61240; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____61237  in
                FStar_Format.reduce1 uu____61234
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
  fun uu____61266  ->
    match uu____61266 with
    | (lineno,file) ->
        let uu____61273 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____61273
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
      let for1 uu____61325 =
        match uu____61325 with
        | (uu____61348,x,mangle_opt,tparams,uu____61352,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____61387 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____61398 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____61398
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____61425 =
                    match uu____61425 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____61438 =
                    let uu____61439 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____61439
                     in
                  FStar_Format.cbrackets uu____61438
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____61480 =
                    match uu____61480 with
                    | (name,tys) ->
                        let uu____61511 = FStar_List.split tys  in
                        (match uu____61511 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____61534 ->
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
              let uu____61565 =
                let uu____61568 =
                  let uu____61571 =
                    let uu____61572 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____61572  in
                  [uu____61571]  in
                tparams1 :: uu____61568  in
              FStar_Format.reduce1 uu____61565  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____61581 =
                   let uu____61584 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____61584; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____61581)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____61592 =
            let uu____61595 =
              let uu____61598 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____61598]  in
            (FStar_Format.text "type") :: uu____61595  in
          FStar_Format.reduce1 uu____61592
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
          let uu____61634 =
            let uu____61637 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____61640 =
              let uu____61643 = doc_of_sig currentModule subsig  in
              let uu____61644 =
                let uu____61647 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____61647]  in
              uu____61643 :: uu____61644  in
            uu____61637 :: uu____61640  in
          FStar_Format.combine FStar_Format.hardline uu____61634
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____61667 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____61667  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____61672,ty)) ->
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
            let uu____61751 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____61751  in
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
          let uu____61767 =
            let uu____61770 =
              let uu____61773 =
                let uu____61776 =
                  let uu____61779 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____61779]  in
                (FStar_Format.text "=") :: uu____61776  in
              (FStar_Format.text "_") :: uu____61773  in
            (FStar_Format.text "let") :: uu____61770  in
          FStar_Format.reduce1 uu____61767
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____61809 ->
                  FStar_Format.empty
              | uu____61810 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____61823  ->
    match uu____61823 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____61893 =
          match uu____61893 with
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
                  (fun uu____61953  ->
                     match uu____61953 with
                     | (s,uu____61959) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____61980 =
                let uu____61983 =
                  let uu____61986 =
                    let uu____61989 = FStar_Format.reduce sub3  in
                    [uu____61989;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____61986
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____61983
                 in
              FStar_Format.reduce uu____61980
        
        and for1_mod istop uu____61992 =
          match uu____61992 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____62074 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____62095 =
                  let uu____62098 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____62098
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
                FStar_Format.reduce1 uu____62095  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____62129  ->
                     match uu____62129 with
                     | (uu____62134,m) -> doc_of_mod target_mod_name m)
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
                let uu____62160 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____62160
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____62168 =
                let uu____62171 =
                  let uu____62174 =
                    let uu____62177 =
                      let uu____62180 =
                        let uu____62183 =
                          let uu____62186 = FStar_Format.reduce sub3  in
                          [uu____62186;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____62183
                         in
                      FStar_Format.hardline :: uu____62180  in
                    FStar_List.append maybe_open_pervasives uu____62177  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____62174
                   in
                FStar_List.append prefix1 uu____62171  in
              FStar_All.pipe_left FStar_Format.reduce uu____62168
         in
        let docs =
          FStar_List.map
            (fun uu____62230  ->
               match uu____62230 with
               | (x,s,m) ->
                   let uu____62287 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____62289 = for1_mod true (x, s, m)  in
                   (uu____62287, uu____62289)) mllib
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
        let uu____62332 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____62332 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____62348 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____62348 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  