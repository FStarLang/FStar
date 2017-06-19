open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
let uu___is_ILeft: assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____4 -> false
let uu___is_IRight: assoc -> Prims.bool =
  fun projectee  -> match projectee with | IRight  -> true | uu____8 -> false
let uu___is_Left: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____12 -> false
let uu___is_Right: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____16 -> false
let uu___is_NonAssoc: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____20 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc
let uu___is_Prefix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____28 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____32 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____37 -> false
let __proj__Infix__item___0: fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int* fixity)
type level = (opprec* assoc)
let t_prio_fun: (Prims.int* fixity) = ((Prims.parse_int "10"), (Infix Right))
let t_prio_tpl: (Prims.int* fixity) =
  ((Prims.parse_int "20"), (Infix NonAssoc))
let t_prio_name: (Prims.int* fixity) = ((Prims.parse_int "30"), Postfix)
let e_bin_prio_lambda: (Prims.int* fixity) = ((Prims.parse_int "5"), Prefix)
let e_bin_prio_if: (Prims.int* fixity) = ((Prims.parse_int "15"), Prefix)
let e_bin_prio_letin: (Prims.int* fixity) = ((Prims.parse_int "19"), Prefix)
let e_bin_prio_or: (Prims.int* fixity) =
  ((Prims.parse_int "20"), (Infix Left))
let e_bin_prio_and: (Prims.int* fixity) =
  ((Prims.parse_int "25"), (Infix Left))
let e_bin_prio_eq: (Prims.int* fixity) =
  ((Prims.parse_int "27"), (Infix NonAssoc))
let e_bin_prio_order: (Prims.int* fixity) =
  ((Prims.parse_int "29"), (Infix NonAssoc))
let e_bin_prio_op1: (Prims.int* fixity) =
  ((Prims.parse_int "30"), (Infix Left))
let e_bin_prio_op2: (Prims.int* fixity) =
  ((Prims.parse_int "40"), (Infix Left))
let e_bin_prio_op3: (Prims.int* fixity) =
  ((Prims.parse_int "50"), (Infix Left))
let e_bin_prio_op4: (Prims.int* fixity) =
  ((Prims.parse_int "60"), (Infix Left))
let e_bin_prio_comb: (Prims.int* fixity) =
  ((Prims.parse_int "70"), (Infix Left))
let e_bin_prio_seq: (Prims.int* fixity) =
  ((Prims.parse_int "100"), (Infix Left))
let e_app_prio: (Prims.int* fixity) =
  ((Prims.parse_int "10000"), (Infix Left))
let min_op_prec: (Prims.int* fixity) =
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let max_op_prec: (Prims.int* fixity) = (FStar_Util.max_int, (Infix NonAssoc))
let rec in_ns x =
  match x with
  | ([],uu____102) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____116,uu____117) -> false
let path_of_ns:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun currentModule  ->
    fun ns  ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns in
      if ns' = currentModule
      then []
      else
        (let cg_libs = FStar_Options.codegen_libs () in
         let ns_len = FStar_List.length ns in
         let found =
           FStar_Util.find_map cg_libs
             (fun cg_path  ->
                let cg_len = FStar_List.length cg_path in
                if (FStar_List.length cg_path) < ns_len
                then
                  let uu____155 = FStar_Util.first_N cg_len ns in
                  match uu____155 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____173 =
                           let uu____175 =
                             let uu____177 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____177] in
                           FStar_List.append pfx uu____175 in
                         Some uu____173
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____194 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____194 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____197 ->
          let uu____198 = x in
          (match uu____198 with
           | (ns,x1) ->
               let uu____203 = path_of_ns currentModule ns in (uu____203, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____209 =
      let uu____210 =
        let uu____211 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____211 in
      let uu____212 = FStar_String.get s (Prims.parse_int "0") in
      uu____210 <> uu____212 in
    if uu____209 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (fst mlp)
      then ptsym_of_symbol (snd mlp)
      else
        (let uu____223 = mlpath_of_mlpath currentModule mlp in
         match uu____223 with
         | (p,s) ->
             let uu____228 =
               let uu____230 =
                 let uu____232 = ptsym_of_symbol s in [uu____232] in
               FStar_List.append p uu____230 in
             FStar_String.concat "." uu____228)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____239 = mlpath_of_mlpath currentModule mlp in
      match uu____239 with
      | (p,s) ->
          let s1 =
            let uu____245 =
              let uu____246 =
                let uu____247 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____247 in
              let uu____248 = FStar_String.get s (Prims.parse_int "0") in
              uu____246 <> uu____248 in
            if uu____245 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s1])
let infix_prim_ops:
  (Prims.string* (Prims.int* fixity)* Prims.string) Prims.list =
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
let prim_uni_ops: (Prims.string* Prims.string) Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")]
let prim_types uu____373 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      option
  =
  fun uu____401  ->
    match uu____401 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____423  ->
               match uu____423 with | (y,uu____430,uu____431) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____445 = as_bin_op p in uu____445 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____468  ->
    match uu____468 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____481  -> match uu____481 with | (y,uu____485) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____492 = as_uni_op p in uu____492 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____509  ->
    match uu____509 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____522  -> match uu____522 with | (y,uu____526) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let uu____533 = as_standard_constructor p in uu____533 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____554  ->
    fun inner  ->
      fun doc1  ->
        match uu____554 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____587 = _inner in
              match uu____587 with
              | (pi,fi) ->
                  let uu____592 = _outer in
                  (match uu____592 with
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
                           | (uu____597,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____598,uu____599) -> false))) in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
let escape_byte_hex: FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let escape_char_hex: FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___117_615  ->
      match uu___117_615 with
      | c when c = '\\' -> "\\\\"
      | c when c = ' ' -> " "
      | c when c = '\b' -> "\\b"
      | c when c = '\t' -> "\\t"
      | c when c = '\r' -> "\\r"
      | c when c = '\n' -> "\\n"
      | c when c = '\'' -> "\\'"
      | c when c = '"' -> "\\\""
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let string_of_mlconstant:
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let uu____634 =
          let uu____635 = escape_or escape_char_hex c in
          Prims.strcat uu____635 "'" in
        Prims.strcat "'" uu____634
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int32 )) ->
        Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int64 )) ->
        Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____649,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____656,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____671 =
          let uu____672 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____672 "\"" in
        Prims.strcat "\"" uu____671
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____674 =
          let uu____675 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____675 "\"" in
        Prims.strcat "\"" uu____674
    | uu____676 ->
        failwith "TODO: extract integer constants properly into OCaml"
let rec doc_of_mltype':
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s '_' 'u'
              else s in
            let uu____698 =
              let uu____699 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____699 in
            FStar_Format.text uu____698
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____707 =
                let uu____708 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____708 in
              FStar_Format.parens uu____707 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____717 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____723 =
                    let uu____724 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____724 in
                  FStar_Format.parens uu____723 in
            let name1 = ptsym currentModule name in
            let uu____726 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____726
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____728,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____736 =
              let uu____737 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____737 in
            maybe_paren outer t_prio_fun uu____736
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____738 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____738
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        doc_of_mltype' currentModule outer
          (FStar_Extraction_ML_Util.resugar_mlty ty)
let rec doc_of_expr:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let uu____790 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____790
            then
              let uu____791 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____791
            else
              (let uu____793 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____793)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____803 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____803
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____805 = string_of_mlconstant c in
            FStar_Format.text uu____805
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____807) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____809 = ptsym currentModule path in
            FStar_Format.text uu____809
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____825 =
              match uu____825 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____833 =
                    let uu____835 =
                      let uu____836 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____836 in
                    [uu____835; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____833 in
            let uu____838 =
              let uu____839 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____839 in
            FStar_Format.cbrackets uu____838
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____846 = is_standard_constructor ctor in
              if uu____846
              then
                let uu____847 =
                  let uu____850 = as_standard_constructor ctor in
                  FStar_Option.get uu____850 in
                snd uu____847
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____862 = is_standard_constructor ctor in
              if uu____862
              then
                let uu____863 =
                  let uu____866 = as_standard_constructor ctor in
                  FStar_Option.get uu____866 in
                snd uu____863
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____882,uu____883) ->
                  let uu____886 =
                    let uu____888 =
                      let uu____890 =
                        let uu____891 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____891 in
                      [uu____890] in
                    (FStar_Format.text name) :: uu____888 in
                  FStar_Format.reduce1 uu____886 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____897 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____897) es in
            let docs2 =
              let uu____901 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____901 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____903,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____913 =
                  let uu____915 =
                    let uu____917 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____917] in
                  FStar_Format.hardline :: uu____915 in
                FStar_Format.reduce uu____913
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____924 =
              let uu____925 =
                let uu____927 =
                  let uu____929 =
                    let uu____931 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____931] in
                  doc1 :: uu____929 in
                pre :: uu____927 in
              FStar_Format.combine FStar_Format.hardline uu____925 in
            FStar_Format.parens uu____924
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____938::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____940;
                    FStar_Extraction_ML_Syntax.loc = uu____941;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____943)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____945;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____946;_}::[])
                 when
                 let uu____964 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____964 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____977;
                            FStar_Extraction_ML_Syntax.loc = uu____978;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____980;
                       FStar_Extraction_ML_Syntax.loc = uu____981;_} when
                       let uu____992 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____993 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____992 = uu____993 -> branches
                   | e2 -> [(FStar_Extraction_ML_Syntax.MLP_Wild, None, e2)] in
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1014;
                   FStar_Extraction_ML_Syntax.loc = uu____1015;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1025;
                   FStar_Extraction_ML_Syntax.loc = uu____1026;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1031 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1042 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1042)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1049 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1049
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1052 =
                   let uu____1054 =
                     let uu____1056 =
                       let uu____1058 =
                         let uu____1059 = ptsym currentModule f in
                         FStar_Format.text uu____1059 in
                       [uu____1058] in
                     (FStar_Format.text ".") :: uu____1056 in
                   e2 :: uu____1054 in
                 FStar_Format.reduce uu____1052) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1077 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1077
              then
                let uu____1078 =
                  let uu____1080 =
                    let uu____1082 =
                      let uu____1084 =
                        match xt with
                        | Some xxt ->
                            let uu____1086 =
                              let uu____1088 =
                                let uu____1090 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1090] in
                              (FStar_Format.text " : ") :: uu____1088 in
                            FStar_Format.reduce1 uu____1086
                        | uu____1091 -> FStar_Format.text "" in
                      [uu____1084; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1082 in
                  (FStar_Format.text "(") :: uu____1080 in
                FStar_Format.reduce1 uu____1078
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1100  ->
                   match uu____1100 with
                   | ((x,uu____1106),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1114 =
                let uu____1116 =
                  let uu____1118 = FStar_Format.reduce1 ids1 in
                  [uu____1118; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1116 in
              FStar_Format.reduce1 uu____1114 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1126 =
                let uu____1128 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1129 =
                  let uu____1131 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1131; FStar_Format.text "end"] in
                uu____1128 :: uu____1129 in
              FStar_Format.combine FStar_Format.hardline uu____1126 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1142 =
                let uu____1144 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1145 =
                  let uu____1147 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1150 =
                    let uu____1152 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1153 =
                      let uu____1155 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1155; FStar_Format.text "end"] in
                    uu____1152 :: uu____1153 in
                  uu____1147 :: uu____1150 in
                uu____1144 :: uu____1145 in
              FStar_Format.combine FStar_Format.hardline uu____1142 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1177 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1177 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1181 =
              let uu____1183 =
                let uu____1185 =
                  let uu____1186 = ptctor currentModule exn in
                  FStar_Format.text uu____1186 in
                [uu____1185] in
              (FStar_Format.text "raise") :: uu____1183 in
            FStar_Format.reduce1 uu____1181
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1195 =
              let uu____1197 =
                let uu____1199 =
                  let uu____1200 = ptctor currentModule exn in
                  FStar_Format.text uu____1200 in
                let uu____1201 =
                  let uu____1203 =
                    let uu____1204 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1204 in
                  [uu____1203] in
                uu____1199 :: uu____1201 in
              (FStar_Format.text "raise") :: uu____1197 in
            FStar_Format.reduce1 uu____1195
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1217 =
              let uu____1219 =
                let uu____1221 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1224 =
                  let uu____1226 =
                    let uu____1228 =
                      let uu____1229 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1229 in
                    [uu____1228] in
                  (FStar_Format.text "with") :: uu____1226 in
                uu____1221 :: uu____1224 in
              (FStar_Format.text "try") :: uu____1219 in
            FStar_Format.combine FStar_Format.hardline uu____1217
and doc_of_binop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____1235 =
            let uu____1241 = as_bin_op p in FStar_Option.get uu____1241 in
          match uu____1235 with
          | (uu____1253,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1 in
              let e21 = doc_of_expr currentModule (prio, Right) e2 in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21] in
              FStar_Format.parens doc1
and doc_of_uniop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____1270 =
          let uu____1273 = as_uni_op p in FStar_Option.get uu____1273 in
        match uu____1270 with
        | (uu____1279,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11] in
            FStar_Format.parens doc1
and doc_of_pattern:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____1288 = string_of_mlconstant c in
          FStar_Format.text uu____1288
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1305 =
            match uu____1305 with
            | (name,p) ->
                let uu____1310 =
                  let uu____1312 =
                    let uu____1313 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1313 in
                  let uu____1315 =
                    let uu____1317 =
                      let uu____1319 = doc_of_pattern currentModule p in
                      [uu____1319] in
                    (FStar_Format.text "=") :: uu____1317 in
                  uu____1312 :: uu____1315 in
                FStar_Format.reduce1 uu____1310 in
          let uu____1320 =
            let uu____1321 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1321 in
          FStar_Format.cbrackets uu____1320
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1328 = is_standard_constructor ctor in
            if uu____1328
            then
              let uu____1329 =
                let uu____1332 = as_standard_constructor ctor in
                FStar_Option.get uu____1332 in
              snd uu____1329
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1344 = is_standard_constructor ctor in
            if uu____1344
            then
              let uu____1345 =
                let uu____1348 = as_standard_constructor ctor in
                FStar_Option.get uu____1348 in
              snd uu____1345
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1360 =
                  let uu____1362 =
                    let uu____1363 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1363 in
                  let uu____1364 =
                    let uu____1366 =
                      let uu____1368 = doc_of_pattern currentModule xs in
                      [uu____1368] in
                    (FStar_Format.text "::") :: uu____1366 in
                  uu____1362 :: uu____1364 in
                FStar_Format.reduce uu____1360
            | (uu____1369,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1370)::[]) ->
                let uu____1373 =
                  let uu____1375 =
                    let uu____1377 =
                      let uu____1378 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1378 in
                    [uu____1377] in
                  (FStar_Format.text name) :: uu____1375 in
                FStar_Format.reduce1 uu____1373
            | uu____1379 ->
                let uu____1383 =
                  let uu____1385 =
                    let uu____1387 =
                      let uu____1388 =
                        let uu____1389 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1389 in
                      FStar_Format.parens uu____1388 in
                    [uu____1387] in
                  (FStar_Format.text name) :: uu____1385 in
                FStar_Format.reduce1 uu____1383 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1397 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1397
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1405  ->
      match uu____1405 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1412 =
                  let uu____1414 =
                    let uu____1416 = doc_of_pattern currentModule p in
                    [uu____1416] in
                  (FStar_Format.text "|") :: uu____1414 in
                FStar_Format.reduce1 uu____1412
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1421 =
                  let uu____1423 =
                    let uu____1425 = doc_of_pattern currentModule p in
                    [uu____1425; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1423 in
                FStar_Format.reduce1 uu____1421 in
          let uu____1426 =
            let uu____1428 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1429 =
              let uu____1431 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1431; FStar_Format.text "end"] in
            uu____1428 :: uu____1429 in
          FStar_Format.combine FStar_Format.hardline uu____1426
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1435  ->
      match uu____1435 with
      | (rec_,top_level,lets) ->
          let for1 uu____1448 =
            match uu____1448 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1451;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1462 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1462
                     then
                       match tys with
                       | Some (uu____1463::uu____1464,uu____1465) ->
                           FStar_Format.text ""
                       | None  -> FStar_Format.text ""
                       | Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | None  -> FStar_Format.text ""
                          | Some (uu____1480::uu____1481,uu____1482) ->
                              FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1497 =
                  let uu____1499 =
                    let uu____1500 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1500 in
                  let uu____1501 =
                    let uu____1503 = FStar_Format.reduce1 ids in
                    [uu____1503; ty_annot; FStar_Format.text "="; e1] in
                  uu____1499 :: uu____1501 in
                FStar_Format.reduce1 uu____1497 in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then
              FStar_Format.reduce1
                [FStar_Format.text "let"; FStar_Format.text "rec"]
            else FStar_Format.text "let" in
          let lets1 = FStar_List.map for1 lets in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   FStar_Format.reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else FStar_Format.text "and";
                     doc1]) lets1 in
          FStar_Format.combine FStar_Format.hardline lets2
and doc_of_loc: FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____1513  ->
    match uu____1513 with
    | (lineno,file) ->
        let uu____1516 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1516
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])
let doc_of_mltydecl:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____1536 =
        match uu____1536 with
        | (uu____1545,x,mangle_opt,tparams,body) ->
            let x1 = match mangle_opt with | None  -> x | Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1560 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1560
              | uu____1561 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1566 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1566) tparams in
                  let uu____1567 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1567 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1584 =
                    match uu____1584 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1593 =
                    let uu____1594 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1594 in
                  FStar_Format.cbrackets uu____1593
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1613 =
                    match uu____1613 with
                    | (name,tys) ->
                        let uu____1627 = FStar_List.split tys in
                        (match uu____1627 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1638 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1 in
                                  let tys3 =
                                    FStar_Format.combine
                                      (FStar_Format.text " * ") tys2 in
                                  FStar_Format.reduce1
                                    [FStar_Format.text name;
                                    FStar_Format.text "of";
                                    tys3])) in
                  let ctors1 = FStar_List.map forctor ctors in
                  let ctors2 =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors1 in
                  FStar_Format.combine FStar_Format.hardline ctors2 in
            let doc1 =
              let uu____1656 =
                let uu____1658 =
                  let uu____1660 =
                    let uu____1661 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1661 in
                  [uu____1660] in
                tparams1 :: uu____1658 in
              FStar_Format.reduce1 uu____1656 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1665 =
                   let uu____1667 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1667; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1665) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1682 =
            let uu____1684 =
              let uu____1686 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1686] in
            (FStar_Format.text "type") :: uu____1684 in
          FStar_Format.reduce1 uu____1682
        else FStar_Format.text "" in
      doc2
let rec doc_of_sig1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____1702 =
            let uu____1704 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1705 =
              let uu____1707 = doc_of_sig currentModule subsig in
              let uu____1708 =
                let uu____1710 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1710] in
              uu____1707 :: uu____1708 in
            uu____1704 :: uu____1705 in
          FStar_Format.combine FStar_Format.hardline uu____1702
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1722 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1722 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1724,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and doc_of_sig:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      let docs1 = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs2 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs1 in
      FStar_Format.reduce docs2
let doc_of_mod1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,args) ->
          let args1 = FStar_List.map FStar_Pervasives.snd args in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1 in
          let args3 =
            let uu____1768 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1768 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1771,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1777 =
            let uu____1779 =
              let uu____1781 =
                let uu____1783 =
                  let uu____1785 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1785] in
                (FStar_Format.text "=") :: uu____1783 in
              (FStar_Format.text "_") :: uu____1781 in
            (FStar_Format.text "let") :: uu____1779 in
          FStar_Format.reduce1 uu____1777
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let doc_of_mod:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs1 =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1801 ->
                  FStar_Format.empty
              | uu____1802 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1808  ->
    match uu____1808 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1846 =
          match uu____1846 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head1 =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x1;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"] in
              let tail1 = FStar_Format.reduce1 [FStar_Format.text "end"] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1885  ->
                     match uu____1885 with
                     | (s,uu____1889) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1904 =
                let uu____1906 =
                  let uu____1908 =
                    let uu____1910 = FStar_Format.reduce sub3 in
                    [uu____1910;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1908 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1906 in
              FStar_Format.reduce uu____1904
        and for1_mod istop uu____1913 =
          match uu____1913 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1950 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____1957 =
                  let uu____1959 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____1959
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
                    else [] in
                FStar_Format.reduce1 uu____1957 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1970  ->
                     match uu____1970 with
                     | (uu____1973,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____1991 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____1991
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____1994 =
                let uu____1996 =
                  let uu____1998 =
                    let uu____2000 =
                      let uu____2002 =
                        let uu____2004 =
                          let uu____2006 = FStar_Format.reduce sub3 in
                          [uu____2006;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2004 in
                      FStar_Format.hardline :: uu____2002 in
                    FStar_List.append maybe_open_pervasives uu____2000 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____1998 in
                FStar_List.append prefix1 uu____1996 in
              FStar_All.pipe_left FStar_Format.reduce uu____1994 in
        let docs1 =
          FStar_List.map
            (fun uu____2024  ->
               match uu____2024 with
               | (x,s,m) ->
                   let uu____2051 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2052 = for1_mod true (x, s, m) in
                   (uu____2051, uu____2052)) mllib in
        docs1
let doc_of_mllib:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  = fun mllib  -> doc_of_mllib_r mllib
let string_of_mlexpr:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2072 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2072 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2082 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2082 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1