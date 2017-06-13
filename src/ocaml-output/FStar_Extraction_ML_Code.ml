open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
let uu___is_ILeft: assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____5 -> false
let uu___is_IRight: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____10 -> false
let uu___is_Left: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____15 -> false
let uu___is_Right: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____20 -> false
let uu___is_NonAssoc: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____25 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc
let uu___is_Prefix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____34 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____39 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____45 -> false
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
  | ([],uu____113) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____127,uu____128) -> false
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
                  let uu____175 = FStar_Util.first_N cg_len ns in
                  match uu____175 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____195 =
                           let uu____197 =
                             let uu____199 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____199] in
                           FStar_List.append pfx uu____197 in
                         Some uu____195
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____218 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____218 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____221 ->
          let uu____222 = x in
          (match uu____222 with
           | (ns,x1) ->
               let uu____227 = path_of_ns currentModule ns in (uu____227, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____234 =
      let uu____235 =
        let uu____236 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____236 in
      let uu____237 = FStar_String.get s (Prims.parse_int "0") in
      uu____235 <> uu____237 in
    if uu____234 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (fst mlp)
      then ptsym_of_symbol (snd mlp)
      else
        (let uu____250 = mlpath_of_mlpath currentModule mlp in
         match uu____250 with
         | (p,s) ->
             let uu____255 =
               let uu____257 =
                 let uu____259 = ptsym_of_symbol s in [uu____259] in
               FStar_List.append p uu____257 in
             FStar_String.concat "." uu____255)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____268 = mlpath_of_mlpath currentModule mlp in
      match uu____268 with
      | (p,s) ->
          let s1 =
            let uu____274 =
              let uu____275 =
                let uu____276 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____276 in
              let uu____277 = FStar_String.get s (Prims.parse_int "0") in
              uu____275 <> uu____277 in
            if uu____274 then Prims.strcat "U__" s else s in
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
let prim_types uu____403 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      option
  =
  fun uu____433  ->
    match uu____433 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____455  ->
               match uu____455 with | (y,uu____462,uu____463) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____478 = as_bin_op p in uu____478 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____502  ->
    match uu____502 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____515  -> match uu____515 with | (y,uu____519) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____527 = as_uni_op p in uu____527 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____546  ->
    match uu____546 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____559  -> match uu____559 with | (y,uu____563) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let uu____571 = as_standard_constructor p in uu____571 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____595  ->
    fun inner  ->
      fun doc1  ->
        match uu____595 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____628 = _inner in
              match uu____628 with
              | (pi,fi) ->
                  let uu____633 = _outer in
                  (match uu____633 with
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
                           | (uu____638,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____639,uu____640) -> false))) in
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
    fun uu___118_660  ->
      match uu___118_660 with
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
        let uu____680 =
          let uu____681 = escape_or escape_char_hex c in
          Prims.strcat uu____681 "'" in
        Prims.strcat "'" uu____680
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int32 )) ->
        Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int64 )) ->
        Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____695,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____702,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____717 =
          let uu____718 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____718 "\"" in
        Prims.strcat "\"" uu____717
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____720 =
          let uu____721 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____721 "\"" in
        Prims.strcat "\"" uu____720
    | uu____722 ->
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
            let uu____744 =
              let uu____745 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____745 in
            FStar_Format.text uu____744
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____753 =
                let uu____754 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____754 in
              FStar_Format.parens uu____753 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____763 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____769 =
                    let uu____770 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____770 in
                  FStar_Format.parens uu____769 in
            let name1 = ptsym currentModule name in
            let uu____772 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____772
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____774,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____782 =
              let uu____783 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____783 in
            maybe_paren outer t_prio_fun uu____782
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____784 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____784
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
            let uu____836 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____836
            then
              let uu____837 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____837
            else
              (let uu____839 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____839)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____849 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____849
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____851 = string_of_mlconstant c in
            FStar_Format.text uu____851
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____853) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____855 = ptsym currentModule path in
            FStar_Format.text uu____855
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____871 =
              match uu____871 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____879 =
                    let uu____881 =
                      let uu____882 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____882 in
                    [uu____881; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____879 in
            let uu____884 =
              let uu____885 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____885 in
            FStar_Format.cbrackets uu____884
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____892 = is_standard_constructor ctor in
              if uu____892
              then
                let uu____893 =
                  let uu____896 = as_standard_constructor ctor in
                  FStar_Option.get uu____896 in
                snd uu____893
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____908 = is_standard_constructor ctor in
              if uu____908
              then
                let uu____909 =
                  let uu____912 = as_standard_constructor ctor in
                  FStar_Option.get uu____912 in
                snd uu____909
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____928,uu____929) ->
                  let uu____932 =
                    let uu____934 =
                      let uu____936 =
                        let uu____937 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____937 in
                      [uu____936] in
                    (FStar_Format.text name) :: uu____934 in
                  FStar_Format.reduce1 uu____932 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____943 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____943) es in
            let docs2 =
              let uu____947 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____947 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____949,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____959 =
                  let uu____961 =
                    let uu____963 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____963] in
                  FStar_Format.hardline :: uu____961 in
                FStar_Format.reduce uu____959
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____970 =
              let uu____971 =
                let uu____973 =
                  let uu____975 =
                    let uu____977 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____977] in
                  doc1 :: uu____975 in
                pre :: uu____973 in
              FStar_Format.combine FStar_Format.hardline uu____971 in
            FStar_Format.parens uu____970
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____984::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____986;
                    FStar_Extraction_ML_Syntax.loc = uu____987;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____989)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____991;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____992;_}::[])
                 when
                 let uu____1010 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1010 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1023;
                            FStar_Extraction_ML_Syntax.loc = uu____1024;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1026;
                       FStar_Extraction_ML_Syntax.loc = uu____1027;_} when
                       let uu____1038 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1039 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1038 = uu____1039 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1060;
                   FStar_Extraction_ML_Syntax.loc = uu____1061;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1071;
                   FStar_Extraction_ML_Syntax.loc = uu____1072;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1077 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1088 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1088)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1095 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1095
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1098 =
                   let uu____1100 =
                     let uu____1102 =
                       let uu____1104 =
                         let uu____1105 = ptsym currentModule f in
                         FStar_Format.text uu____1105 in
                       [uu____1104] in
                     (FStar_Format.text ".") :: uu____1102 in
                   e2 :: uu____1100 in
                 FStar_Format.reduce uu____1098) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1123 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1123
              then
                let uu____1124 =
                  let uu____1126 =
                    let uu____1128 =
                      let uu____1130 =
                        match xt with
                        | Some xxt ->
                            let uu____1132 =
                              let uu____1134 =
                                let uu____1136 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1136] in
                              (FStar_Format.text " : ") :: uu____1134 in
                            FStar_Format.reduce1 uu____1132
                        | uu____1137 -> FStar_Format.text "" in
                      [uu____1130; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1128 in
                  (FStar_Format.text "(") :: uu____1126 in
                FStar_Format.reduce1 uu____1124
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1146  ->
                   match uu____1146 with
                   | ((x,uu____1152),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1160 =
                let uu____1162 =
                  let uu____1164 = FStar_Format.reduce1 ids1 in
                  [uu____1164; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1162 in
              FStar_Format.reduce1 uu____1160 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1172 =
                let uu____1174 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1175 =
                  let uu____1177 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1177; FStar_Format.text "end"] in
                uu____1174 :: uu____1175 in
              FStar_Format.combine FStar_Format.hardline uu____1172 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1188 =
                let uu____1190 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1191 =
                  let uu____1193 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1196 =
                    let uu____1198 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1199 =
                      let uu____1201 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1201; FStar_Format.text "end"] in
                    uu____1198 :: uu____1199 in
                  uu____1193 :: uu____1196 in
                uu____1190 :: uu____1191 in
              FStar_Format.combine FStar_Format.hardline uu____1188 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1223 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1223 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1227 =
              let uu____1229 =
                let uu____1231 =
                  let uu____1232 = ptctor currentModule exn in
                  FStar_Format.text uu____1232 in
                [uu____1231] in
              (FStar_Format.text "raise") :: uu____1229 in
            FStar_Format.reduce1 uu____1227
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1241 =
              let uu____1243 =
                let uu____1245 =
                  let uu____1246 = ptctor currentModule exn in
                  FStar_Format.text uu____1246 in
                let uu____1247 =
                  let uu____1249 =
                    let uu____1250 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1250 in
                  [uu____1249] in
                uu____1245 :: uu____1247 in
              (FStar_Format.text "raise") :: uu____1243 in
            FStar_Format.reduce1 uu____1241
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1263 =
              let uu____1265 =
                let uu____1267 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1270 =
                  let uu____1272 =
                    let uu____1274 =
                      let uu____1275 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1275 in
                    [uu____1274] in
                  (FStar_Format.text "with") :: uu____1272 in
                uu____1267 :: uu____1270 in
              (FStar_Format.text "try") :: uu____1265 in
            FStar_Format.combine FStar_Format.hardline uu____1263
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
          let uu____1281 =
            let uu____1287 = as_bin_op p in FStar_Option.get uu____1287 in
          match uu____1281 with
          | (uu____1299,prio,txt) ->
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
        let uu____1316 =
          let uu____1319 = as_uni_op p in FStar_Option.get uu____1319 in
        match uu____1316 with
        | (uu____1325,txt) ->
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
          let uu____1334 = string_of_mlconstant c in
          FStar_Format.text uu____1334
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1351 =
            match uu____1351 with
            | (name,p) ->
                let uu____1356 =
                  let uu____1358 =
                    let uu____1359 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1359 in
                  let uu____1361 =
                    let uu____1363 =
                      let uu____1365 = doc_of_pattern currentModule p in
                      [uu____1365] in
                    (FStar_Format.text "=") :: uu____1363 in
                  uu____1358 :: uu____1361 in
                FStar_Format.reduce1 uu____1356 in
          let uu____1366 =
            let uu____1367 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1367 in
          FStar_Format.cbrackets uu____1366
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1374 = is_standard_constructor ctor in
            if uu____1374
            then
              let uu____1375 =
                let uu____1378 = as_standard_constructor ctor in
                FStar_Option.get uu____1378 in
              snd uu____1375
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1390 = is_standard_constructor ctor in
            if uu____1390
            then
              let uu____1391 =
                let uu____1394 = as_standard_constructor ctor in
                FStar_Option.get uu____1394 in
              snd uu____1391
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1406 =
                  let uu____1408 =
                    let uu____1409 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1409 in
                  let uu____1410 =
                    let uu____1412 =
                      let uu____1414 = doc_of_pattern currentModule xs in
                      [uu____1414] in
                    (FStar_Format.text "::") :: uu____1412 in
                  uu____1408 :: uu____1410 in
                FStar_Format.reduce uu____1406
            | (uu____1415,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1416)::[]) ->
                let uu____1419 =
                  let uu____1421 =
                    let uu____1423 =
                      let uu____1424 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1424 in
                    [uu____1423] in
                  (FStar_Format.text name) :: uu____1421 in
                FStar_Format.reduce1 uu____1419
            | uu____1425 ->
                let uu____1429 =
                  let uu____1431 =
                    let uu____1433 =
                      let uu____1434 =
                        let uu____1435 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1435 in
                      FStar_Format.parens uu____1434 in
                    [uu____1433] in
                  (FStar_Format.text name) :: uu____1431 in
                FStar_Format.reduce1 uu____1429 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1443 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1443
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1451  ->
      match uu____1451 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1458 =
                  let uu____1460 =
                    let uu____1462 = doc_of_pattern currentModule p in
                    [uu____1462] in
                  (FStar_Format.text "|") :: uu____1460 in
                FStar_Format.reduce1 uu____1458
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1467 =
                  let uu____1469 =
                    let uu____1471 = doc_of_pattern currentModule p in
                    [uu____1471; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1469 in
                FStar_Format.reduce1 uu____1467 in
          let uu____1472 =
            let uu____1474 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1475 =
              let uu____1477 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1477; FStar_Format.text "end"] in
            uu____1474 :: uu____1475 in
          FStar_Format.combine FStar_Format.hardline uu____1472
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1481  ->
      match uu____1481 with
      | (rec_,top_level,lets) ->
          let for1 uu____1494 =
            match uu____1494 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1497;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ids1 =
                  FStar_List.map
                    (fun uu____1514  ->
                       match uu____1514 with
                       | (x,uu____1518) -> FStar_Format.text x) ids in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1521 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1521
                     then
                       match tys with
                       | Some (uu____1522::uu____1523,uu____1524) ->
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
                          | Some (uu____1539::uu____1540,uu____1541) ->
                              FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1556 =
                  let uu____1558 =
                    let uu____1559 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1559 in
                  let uu____1560 =
                    let uu____1562 = FStar_Format.reduce1 ids1 in
                    [uu____1562; ty_annot; FStar_Format.text "="; e1] in
                  uu____1558 :: uu____1560 in
                FStar_Format.reduce1 uu____1556 in
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
  fun uu____1572  ->
    match uu____1572 with
    | (lineno,file) ->
        let uu____1575 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1575
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
      let for1 uu____1597 =
        match uu____1597 with
        | (uu____1606,x,mangle_opt,tparams,body) ->
            let x1 = match mangle_opt with | None  -> x | Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1621 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1621
              | uu____1622 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1627 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1627) tparams in
                  let uu____1628 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1628 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1645 =
                    match uu____1645 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1654 =
                    let uu____1655 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1655 in
                  FStar_Format.cbrackets uu____1654
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1674 =
                    match uu____1674 with
                    | (name,tys) ->
                        let uu____1688 = FStar_List.split tys in
                        (match uu____1688 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1699 ->
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
              let uu____1717 =
                let uu____1719 =
                  let uu____1721 =
                    let uu____1722 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1722 in
                  [uu____1721] in
                tparams1 :: uu____1719 in
              FStar_Format.reduce1 uu____1717 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1726 =
                   let uu____1728 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1728; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1726) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1746 =
            let uu____1748 =
              let uu____1750 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1750] in
            (FStar_Format.text "type") :: uu____1748 in
          FStar_Format.reduce1 uu____1746
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
          let uu____1766 =
            let uu____1768 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1769 =
              let uu____1771 = doc_of_sig currentModule subsig in
              let uu____1772 =
                let uu____1774 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1774] in
              uu____1771 :: uu____1772 in
            uu____1768 :: uu____1769 in
          FStar_Format.combine FStar_Format.hardline uu____1766
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1786 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1786 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1788,ty)) ->
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
            let uu____1834 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1834 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1837,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1843 =
            let uu____1845 =
              let uu____1847 =
                let uu____1849 =
                  let uu____1851 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1851] in
                (FStar_Format.text "=") :: uu____1849 in
              (FStar_Format.text "_") :: uu____1847 in
            (FStar_Format.text "let") :: uu____1845 in
          FStar_Format.reduce1 uu____1843
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1869 ->
                  FStar_Format.empty
              | uu____1870 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1877  ->
    match uu____1877 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1915 =
          match uu____1915 with
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
                  (fun uu____1954  ->
                     match uu____1954 with
                     | (s,uu____1958) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1973 =
                let uu____1975 =
                  let uu____1977 =
                    let uu____1979 = FStar_Format.reduce sub3 in
                    [uu____1979;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1977 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1975 in
              FStar_Format.reduce uu____1973
        and for1_mod istop uu____1982 =
          match uu____1982 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____2019 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____2026 =
                  let uu____2028 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____2028
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
                FStar_Format.reduce1 uu____2026 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____2039  ->
                     match uu____2039 with
                     | (uu____2042,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____2060 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____2060
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____2063 =
                let uu____2065 =
                  let uu____2067 =
                    let uu____2069 =
                      let uu____2071 =
                        let uu____2073 =
                          let uu____2075 = FStar_Format.reduce sub3 in
                          [uu____2075;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2073 in
                      FStar_Format.hardline :: uu____2071 in
                    FStar_List.append maybe_open_pervasives uu____2069 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____2067 in
                FStar_List.append prefix1 uu____2065 in
              FStar_All.pipe_left FStar_Format.reduce uu____2063 in
        let docs1 =
          FStar_List.map
            (fun uu____2093  ->
               match uu____2093 with
               | (x,s,m) ->
                   let uu____2120 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2121 = for1_mod true (x, s, m) in
                   (uu____2120, uu____2121)) mllib in
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
        let uu____2144 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2144 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2156 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2156 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1