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
                  let uu____162 = FStar_Util.first_N cg_len ns in
                  match uu____162 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____182 =
                           let uu____184 =
                             let uu____186 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____186] in
                           FStar_List.append pfx uu____184 in
                         Some uu____182
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____203 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____203 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____206 ->
          let uu____207 = x in
          (match uu____207 with
           | (ns,x1) ->
               let uu____212 = path_of_ns currentModule ns in (uu____212, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____218 =
      let uu____219 =
        let uu____220 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____220 in
      let uu____221 = FStar_String.get s (Prims.parse_int "0") in
      uu____219 <> uu____221 in
    if uu____218 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (fst mlp)
      then ptsym_of_symbol (snd mlp)
      else
        (let uu____232 = mlpath_of_mlpath currentModule mlp in
         match uu____232 with
         | (p,s) ->
             let uu____237 =
               let uu____239 =
                 let uu____241 = ptsym_of_symbol s in [uu____241] in
               FStar_List.append p uu____239 in
             FStar_String.concat "." uu____237)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____248 = mlpath_of_mlpath currentModule mlp in
      match uu____248 with
      | (p,s) ->
          let s1 =
            let uu____254 =
              let uu____255 =
                let uu____256 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____256 in
              let uu____257 = FStar_String.get s (Prims.parse_int "0") in
              uu____255 <> uu____257 in
            if uu____254 then Prims.strcat "U__" s else s in
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
let prim_types uu____382 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      option
  =
  fun uu____410  ->
    match uu____410 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____432  ->
               match uu____432 with | (y,uu____439,uu____440) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____454 = as_bin_op p in uu____454 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____477  ->
    match uu____477 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____490  -> match uu____490 with | (y,uu____494) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____501 = as_uni_op p in uu____501 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____518  ->
    match uu____518 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____531  -> match uu____531 with | (y,uu____535) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let uu____542 = as_standard_constructor p in uu____542 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____563  ->
    fun inner  ->
      fun doc1  ->
        match uu____563 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____596 = _inner in
              match uu____596 with
              | (pi,fi) ->
                  let uu____601 = _outer in
                  (match uu____601 with
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
                           | (uu____606,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____607,uu____608) -> false))) in
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
    fun uu___118_624  ->
      match uu___118_624 with
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
        let uu____643 =
          let uu____644 = escape_or escape_char_hex c in
          Prims.strcat uu____644 "'" in
        Prims.strcat "'" uu____643
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int32 )) ->
        Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int64 )) ->
        Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____658,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____665,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____680 =
          let uu____681 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____681 "\"" in
        Prims.strcat "\"" uu____680
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____683 =
          let uu____684 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____684 "\"" in
        Prims.strcat "\"" uu____683
    | uu____685 ->
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
            let uu____707 =
              let uu____708 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____708 in
            FStar_Format.text uu____707
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____716 =
                let uu____717 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____717 in
              FStar_Format.parens uu____716 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____726 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____732 =
                    let uu____733 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____733 in
                  FStar_Format.parens uu____732 in
            let name1 = ptsym currentModule name in
            let uu____735 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____735
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____737,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____745 =
              let uu____746 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____746 in
            maybe_paren outer t_prio_fun uu____745
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____747 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____747
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
            let uu____799 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____799
            then
              let uu____800 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____800
            else
              (let uu____802 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____802)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____812 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____812
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____814 = string_of_mlconstant c in
            FStar_Format.text uu____814
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____816) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____818 = ptsym currentModule path in
            FStar_Format.text uu____818
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____834 =
              match uu____834 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____842 =
                    let uu____844 =
                      let uu____845 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____845 in
                    [uu____844; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____842 in
            let uu____847 =
              let uu____848 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____848 in
            FStar_Format.cbrackets uu____847
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____855 = is_standard_constructor ctor in
              if uu____855
              then
                let uu____856 =
                  let uu____859 = as_standard_constructor ctor in
                  FStar_Option.get uu____859 in
                snd uu____856
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____871 = is_standard_constructor ctor in
              if uu____871
              then
                let uu____872 =
                  let uu____875 = as_standard_constructor ctor in
                  FStar_Option.get uu____875 in
                snd uu____872
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____891,uu____892) ->
                  let uu____895 =
                    let uu____897 =
                      let uu____899 =
                        let uu____900 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____900 in
                      [uu____899] in
                    (FStar_Format.text name) :: uu____897 in
                  FStar_Format.reduce1 uu____895 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____906 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____906) es in
            let docs2 =
              let uu____910 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____910 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____912,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____922 =
                  let uu____924 =
                    let uu____926 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____926] in
                  FStar_Format.hardline :: uu____924 in
                FStar_Format.reduce uu____922
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____933 =
              let uu____934 =
                let uu____936 =
                  let uu____938 =
                    let uu____940 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____940] in
                  doc1 :: uu____938 in
                pre :: uu____936 in
              FStar_Format.combine FStar_Format.hardline uu____934 in
            FStar_Format.parens uu____933
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____947::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____949;
                    FStar_Extraction_ML_Syntax.loc = uu____950;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____952)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____954;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____955;_}::[])
                 when
                 let uu____973 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____973 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____986;
                            FStar_Extraction_ML_Syntax.loc = uu____987;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____989;
                       FStar_Extraction_ML_Syntax.loc = uu____990;_} when
                       let uu____1001 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1002 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1001 = uu____1002 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1023;
                   FStar_Extraction_ML_Syntax.loc = uu____1024;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1034;
                   FStar_Extraction_ML_Syntax.loc = uu____1035;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1040 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1051 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1051)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1058 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1058
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1061 =
                   let uu____1063 =
                     let uu____1065 =
                       let uu____1067 =
                         let uu____1068 = ptsym currentModule f in
                         FStar_Format.text uu____1068 in
                       [uu____1067] in
                     (FStar_Format.text ".") :: uu____1065 in
                   e2 :: uu____1063 in
                 FStar_Format.reduce uu____1061) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1086 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1086
              then
                let uu____1087 =
                  let uu____1089 =
                    let uu____1091 =
                      let uu____1093 =
                        match xt with
                        | Some xxt ->
                            let uu____1095 =
                              let uu____1097 =
                                let uu____1099 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1099] in
                              (FStar_Format.text " : ") :: uu____1097 in
                            FStar_Format.reduce1 uu____1095
                        | uu____1100 -> FStar_Format.text "" in
                      [uu____1093; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1091 in
                  (FStar_Format.text "(") :: uu____1089 in
                FStar_Format.reduce1 uu____1087
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1109  ->
                   match uu____1109 with
                   | ((x,uu____1115),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1123 =
                let uu____1125 =
                  let uu____1127 = FStar_Format.reduce1 ids1 in
                  [uu____1127; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1125 in
              FStar_Format.reduce1 uu____1123 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1135 =
                let uu____1137 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1138 =
                  let uu____1140 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1140; FStar_Format.text "end"] in
                uu____1137 :: uu____1138 in
              FStar_Format.combine FStar_Format.hardline uu____1135 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1151 =
                let uu____1153 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1154 =
                  let uu____1156 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1159 =
                    let uu____1161 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1162 =
                      let uu____1164 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1164; FStar_Format.text "end"] in
                    uu____1161 :: uu____1162 in
                  uu____1156 :: uu____1159 in
                uu____1153 :: uu____1154 in
              FStar_Format.combine FStar_Format.hardline uu____1151 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1186 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1186 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1190 =
              let uu____1192 =
                let uu____1194 =
                  let uu____1195 = ptctor currentModule exn in
                  FStar_Format.text uu____1195 in
                [uu____1194] in
              (FStar_Format.text "raise") :: uu____1192 in
            FStar_Format.reduce1 uu____1190
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1204 =
              let uu____1206 =
                let uu____1208 =
                  let uu____1209 = ptctor currentModule exn in
                  FStar_Format.text uu____1209 in
                let uu____1210 =
                  let uu____1212 =
                    let uu____1213 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1213 in
                  [uu____1212] in
                uu____1208 :: uu____1210 in
              (FStar_Format.text "raise") :: uu____1206 in
            FStar_Format.reduce1 uu____1204
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1226 =
              let uu____1228 =
                let uu____1230 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1233 =
                  let uu____1235 =
                    let uu____1237 =
                      let uu____1238 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1238 in
                    [uu____1237] in
                  (FStar_Format.text "with") :: uu____1235 in
                uu____1230 :: uu____1233 in
              (FStar_Format.text "try") :: uu____1228 in
            FStar_Format.combine FStar_Format.hardline uu____1226
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
          let uu____1244 =
            let uu____1250 = as_bin_op p in FStar_Option.get uu____1250 in
          match uu____1244 with
          | (uu____1262,prio,txt) ->
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
        let uu____1279 =
          let uu____1282 = as_uni_op p in FStar_Option.get uu____1282 in
        match uu____1279 with
        | (uu____1288,txt) ->
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
          let uu____1297 = string_of_mlconstant c in
          FStar_Format.text uu____1297
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1314 =
            match uu____1314 with
            | (name,p) ->
                let uu____1319 =
                  let uu____1321 =
                    let uu____1322 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1322 in
                  let uu____1324 =
                    let uu____1326 =
                      let uu____1328 = doc_of_pattern currentModule p in
                      [uu____1328] in
                    (FStar_Format.text "=") :: uu____1326 in
                  uu____1321 :: uu____1324 in
                FStar_Format.reduce1 uu____1319 in
          let uu____1329 =
            let uu____1330 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1330 in
          FStar_Format.cbrackets uu____1329
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1337 = is_standard_constructor ctor in
            if uu____1337
            then
              let uu____1338 =
                let uu____1341 = as_standard_constructor ctor in
                FStar_Option.get uu____1341 in
              snd uu____1338
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1353 = is_standard_constructor ctor in
            if uu____1353
            then
              let uu____1354 =
                let uu____1357 = as_standard_constructor ctor in
                FStar_Option.get uu____1357 in
              snd uu____1354
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1369 =
                  let uu____1371 =
                    let uu____1372 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1372 in
                  let uu____1373 =
                    let uu____1375 =
                      let uu____1377 = doc_of_pattern currentModule xs in
                      [uu____1377] in
                    (FStar_Format.text "::") :: uu____1375 in
                  uu____1371 :: uu____1373 in
                FStar_Format.reduce uu____1369
            | (uu____1378,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1379)::[]) ->
                let uu____1382 =
                  let uu____1384 =
                    let uu____1386 =
                      let uu____1387 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1387 in
                    [uu____1386] in
                  (FStar_Format.text name) :: uu____1384 in
                FStar_Format.reduce1 uu____1382
            | uu____1388 ->
                let uu____1392 =
                  let uu____1394 =
                    let uu____1396 =
                      let uu____1397 =
                        let uu____1398 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1398 in
                      FStar_Format.parens uu____1397 in
                    [uu____1396] in
                  (FStar_Format.text name) :: uu____1394 in
                FStar_Format.reduce1 uu____1392 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1406 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1406
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1414  ->
      match uu____1414 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1421 =
                  let uu____1423 =
                    let uu____1425 = doc_of_pattern currentModule p in
                    [uu____1425] in
                  (FStar_Format.text "|") :: uu____1423 in
                FStar_Format.reduce1 uu____1421
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1430 =
                  let uu____1432 =
                    let uu____1434 = doc_of_pattern currentModule p in
                    [uu____1434; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1432 in
                FStar_Format.reduce1 uu____1430 in
          let uu____1435 =
            let uu____1437 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1438 =
              let uu____1440 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1440; FStar_Format.text "end"] in
            uu____1437 :: uu____1438 in
          FStar_Format.combine FStar_Format.hardline uu____1435
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1444  ->
      match uu____1444 with
      | (rec_,top_level,lets) ->
          let for1 uu____1457 =
            match uu____1457 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1460;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1471 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1471
                     then
                       match tys with
                       | Some (uu____1472::uu____1473,uu____1474) ->
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
                          | Some (uu____1489::uu____1490,uu____1491) ->
                              FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1506 =
                  let uu____1508 =
                    let uu____1509 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1509 in
                  let uu____1510 =
                    let uu____1512 = FStar_Format.reduce1 ids in
                    [uu____1512; ty_annot; FStar_Format.text "="; e1] in
                  uu____1508 :: uu____1510 in
                FStar_Format.reduce1 uu____1506 in
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
  fun uu____1522  ->
    match uu____1522 with
    | (lineno,file) ->
        let uu____1525 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1525
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
      let for1 uu____1545 =
        match uu____1545 with
        | (uu____1554,x,mangle_opt,tparams,body) ->
            let x1 = match mangle_opt with | None  -> x | Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1569 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1569
              | uu____1570 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1575 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1575) tparams in
                  let uu____1576 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1576 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1593 =
                    match uu____1593 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1602 =
                    let uu____1603 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1603 in
                  FStar_Format.cbrackets uu____1602
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1622 =
                    match uu____1622 with
                    | (name,tys) ->
                        let uu____1636 = FStar_List.split tys in
                        (match uu____1636 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1647 ->
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
              let uu____1665 =
                let uu____1667 =
                  let uu____1669 =
                    let uu____1670 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1670 in
                  [uu____1669] in
                tparams1 :: uu____1667 in
              FStar_Format.reduce1 uu____1665 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1674 =
                   let uu____1676 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1676; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1674) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1694 =
            let uu____1696 =
              let uu____1698 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1698] in
            (FStar_Format.text "type") :: uu____1696 in
          FStar_Format.reduce1 uu____1694
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
          let uu____1714 =
            let uu____1716 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1717 =
              let uu____1719 = doc_of_sig currentModule subsig in
              let uu____1720 =
                let uu____1722 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1722] in
              uu____1719 :: uu____1720 in
            uu____1716 :: uu____1717 in
          FStar_Format.combine FStar_Format.hardline uu____1714
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1734 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1734 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1736,ty)) ->
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
            let uu____1780 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1780 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1783,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1789 =
            let uu____1791 =
              let uu____1793 =
                let uu____1795 =
                  let uu____1797 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1797] in
                (FStar_Format.text "=") :: uu____1795 in
              (FStar_Format.text "_") :: uu____1793 in
            (FStar_Format.text "let") :: uu____1791 in
          FStar_Format.reduce1 uu____1789
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1813 ->
                  FStar_Format.empty
              | uu____1814 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1820  ->
    match uu____1820 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1858 =
          match uu____1858 with
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
                  (fun uu____1897  ->
                     match uu____1897 with
                     | (s,uu____1901) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1916 =
                let uu____1918 =
                  let uu____1920 =
                    let uu____1922 = FStar_Format.reduce sub3 in
                    [uu____1922;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1920 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1918 in
              FStar_Format.reduce uu____1916
        and for1_mod istop uu____1925 =
          match uu____1925 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1962 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____1969 =
                  let uu____1971 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____1971
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
                FStar_Format.reduce1 uu____1969 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1982  ->
                     match uu____1982 with
                     | (uu____1985,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____2003 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____2003
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____2006 =
                let uu____2008 =
                  let uu____2010 =
                    let uu____2012 =
                      let uu____2014 =
                        let uu____2016 =
                          let uu____2018 = FStar_Format.reduce sub3 in
                          [uu____2018;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2016 in
                      FStar_Format.hardline :: uu____2014 in
                    FStar_List.append maybe_open_pervasives uu____2012 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____2010 in
                FStar_List.append prefix1 uu____2008 in
              FStar_All.pipe_left FStar_Format.reduce uu____2006 in
        let docs1 =
          FStar_List.map
            (fun uu____2036  ->
               match uu____2036 with
               | (x,s,m) ->
                   let uu____2063 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2064 = for1_mod true (x, s, m) in
                   (uu____2063, uu____2064)) mllib in
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
        let uu____2084 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2084 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2094 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2094 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1