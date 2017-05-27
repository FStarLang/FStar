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
    match projectee with | Prefix  -> true | uu____27 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____31 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____36 -> false
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
  | ([],uu____101) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____115,uu____116) -> false
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
                  let uu____154 = FStar_Util.first_N cg_len ns in
                  match uu____154 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____172 =
                           let uu____174 =
                             let uu____176 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____176] in
                           FStar_List.append pfx uu____174 in
                         Some uu____172
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____193 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____193 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____196 ->
          let uu____197 = x in
          (match uu____197 with
           | (ns,x1) ->
               let uu____202 = path_of_ns currentModule ns in (uu____202, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____208 =
      let uu____209 =
        let uu____210 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____210 in
      let uu____211 = FStar_String.get s (Prims.parse_int "0") in
      uu____209 <> uu____211 in
    if uu____208 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (fst mlp)
      then ptsym_of_symbol (snd mlp)
      else
        (let uu____222 = mlpath_of_mlpath currentModule mlp in
         match uu____222 with
         | (p,s) ->
             let uu____227 =
               let uu____229 =
                 let uu____231 = ptsym_of_symbol s in [uu____231] in
               FStar_List.append p uu____229 in
             FStar_String.concat "." uu____227)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____238 = mlpath_of_mlpath currentModule mlp in
      match uu____238 with
      | (p,s) ->
          let s1 =
            let uu____244 =
              let uu____245 =
                let uu____246 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____246 in
              let uu____247 = FStar_String.get s (Prims.parse_int "0") in
              uu____245 <> uu____247 in
            if uu____244 then Prims.strcat "U__" s else s in
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
let prim_types uu____372 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      option
  =
  fun uu____400  ->
    match uu____400 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____422  ->
               match uu____422 with | (y,uu____429,uu____430) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____444 = as_bin_op p in uu____444 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____467  ->
    match uu____467 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____480  -> match uu____480 with | (y,uu____484) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____491 = as_uni_op p in uu____491 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____508  ->
    match uu____508 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____521  -> match uu____521 with | (y,uu____525) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let uu____532 = as_standard_constructor p in uu____532 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____553  ->
    fun inner  ->
      fun doc1  ->
        match uu____553 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____586 = _inner in
              match uu____586 with
              | (pi,fi) ->
                  let uu____591 = _outer in
                  (match uu____591 with
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
                           | (uu____596,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____597,uu____598) -> false))) in
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
    fun uu___118_614  ->
      match uu___118_614 with
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
        let uu____633 =
          let uu____634 = escape_or escape_char_hex c in
          Prims.strcat uu____634 "'" in
        Prims.strcat "'" uu____633
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int32 )) ->
        Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int64 )) ->
        Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____648,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____655,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____670 =
          let uu____671 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____671 "\"" in
        Prims.strcat "\"" uu____670
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____673 =
          let uu____674 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____674 "\"" in
        Prims.strcat "\"" uu____673
    | uu____675 ->
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
            let uu____697 =
              let uu____698 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____698 in
            FStar_Format.text uu____697
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____706 =
                let uu____707 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____707 in
              FStar_Format.parens uu____706 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____716 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____722 =
                    let uu____723 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____723 in
                  FStar_Format.parens uu____722 in
            let name1 = ptsym currentModule name in
            let uu____725 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____725
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____727,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____735 =
              let uu____736 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____736 in
            maybe_paren outer t_prio_fun uu____735
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____737 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____737
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
            let uu____789 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____789
            then
              let uu____790 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____790
            else
              (let uu____792 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____792)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____802 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____802
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____804 = string_of_mlconstant c in
            FStar_Format.text uu____804
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____806) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____808 = ptsym currentModule path in
            FStar_Format.text uu____808
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____824 =
              match uu____824 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____832 =
                    let uu____834 =
                      let uu____835 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____835 in
                    [uu____834; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____832 in
            let uu____837 =
              let uu____838 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____838 in
            FStar_Format.cbrackets uu____837
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____845 = is_standard_constructor ctor in
              if uu____845
              then
                let uu____846 =
                  let uu____849 = as_standard_constructor ctor in
                  FStar_Option.get uu____849 in
                snd uu____846
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____861 = is_standard_constructor ctor in
              if uu____861
              then
                let uu____862 =
                  let uu____865 = as_standard_constructor ctor in
                  FStar_Option.get uu____865 in
                snd uu____862
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____881,uu____882) ->
                  let uu____885 =
                    let uu____887 =
                      let uu____889 =
                        let uu____890 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____890 in
                      [uu____889] in
                    (FStar_Format.text name) :: uu____887 in
                  FStar_Format.reduce1 uu____885 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____896 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____896) es in
            let docs2 =
              let uu____900 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____900 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____902,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____912 =
                  let uu____914 =
                    let uu____916 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____916] in
                  FStar_Format.hardline :: uu____914 in
                FStar_Format.reduce uu____912
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____923 =
              let uu____924 =
                let uu____926 =
                  let uu____928 =
                    let uu____930 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____930] in
                  doc1 :: uu____928 in
                pre :: uu____926 in
              FStar_Format.combine FStar_Format.hardline uu____924 in
            FStar_Format.parens uu____923
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____937::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____939;
                    FStar_Extraction_ML_Syntax.loc = uu____940;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____942)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____944;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____945;_}::[])
                 when
                 let uu____963 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____963 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____976;
                            FStar_Extraction_ML_Syntax.loc = uu____977;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____979;
                       FStar_Extraction_ML_Syntax.loc = uu____980;_} when
                       let uu____991 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____992 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____991 = uu____992 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1013;
                   FStar_Extraction_ML_Syntax.loc = uu____1014;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1024;
                   FStar_Extraction_ML_Syntax.loc = uu____1025;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1030 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1041 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1041)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1048 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1048
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1051 =
                   let uu____1053 =
                     let uu____1055 =
                       let uu____1057 =
                         let uu____1058 = ptsym currentModule f in
                         FStar_Format.text uu____1058 in
                       [uu____1057] in
                     (FStar_Format.text ".") :: uu____1055 in
                   e2 :: uu____1053 in
                 FStar_Format.reduce uu____1051) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1076 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1076
              then
                let uu____1077 =
                  let uu____1079 =
                    let uu____1081 =
                      let uu____1083 =
                        match xt with
                        | Some xxt ->
                            let uu____1085 =
                              let uu____1087 =
                                let uu____1089 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1089] in
                              (FStar_Format.text " : ") :: uu____1087 in
                            FStar_Format.reduce1 uu____1085
                        | uu____1090 -> FStar_Format.text "" in
                      [uu____1083; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1081 in
                  (FStar_Format.text "(") :: uu____1079 in
                FStar_Format.reduce1 uu____1077
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1099  ->
                   match uu____1099 with
                   | ((x,uu____1105),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1113 =
                let uu____1115 =
                  let uu____1117 = FStar_Format.reduce1 ids1 in
                  [uu____1117; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1115 in
              FStar_Format.reduce1 uu____1113 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1125 =
                let uu____1127 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1128 =
                  let uu____1130 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1130; FStar_Format.text "end"] in
                uu____1127 :: uu____1128 in
              FStar_Format.combine FStar_Format.hardline uu____1125 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1141 =
                let uu____1143 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1144 =
                  let uu____1146 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1149 =
                    let uu____1151 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1152 =
                      let uu____1154 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1154; FStar_Format.text "end"] in
                    uu____1151 :: uu____1152 in
                  uu____1146 :: uu____1149 in
                uu____1143 :: uu____1144 in
              FStar_Format.combine FStar_Format.hardline uu____1141 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1176 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1176 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1180 =
              let uu____1182 =
                let uu____1184 =
                  let uu____1185 = ptctor currentModule exn in
                  FStar_Format.text uu____1185 in
                [uu____1184] in
              (FStar_Format.text "raise") :: uu____1182 in
            FStar_Format.reduce1 uu____1180
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1194 =
              let uu____1196 =
                let uu____1198 =
                  let uu____1199 = ptctor currentModule exn in
                  FStar_Format.text uu____1199 in
                let uu____1200 =
                  let uu____1202 =
                    let uu____1203 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1203 in
                  [uu____1202] in
                uu____1198 :: uu____1200 in
              (FStar_Format.text "raise") :: uu____1196 in
            FStar_Format.reduce1 uu____1194
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1216 =
              let uu____1218 =
                let uu____1220 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1223 =
                  let uu____1225 =
                    let uu____1227 =
                      let uu____1228 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1228 in
                    [uu____1227] in
                  (FStar_Format.text "with") :: uu____1225 in
                uu____1220 :: uu____1223 in
              (FStar_Format.text "try") :: uu____1218 in
            FStar_Format.combine FStar_Format.hardline uu____1216
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
          let uu____1234 =
            let uu____1240 = as_bin_op p in FStar_Option.get uu____1240 in
          match uu____1234 with
          | (uu____1252,prio,txt) ->
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
        let uu____1269 =
          let uu____1272 = as_uni_op p in FStar_Option.get uu____1272 in
        match uu____1269 with
        | (uu____1278,txt) ->
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
          let uu____1287 = string_of_mlconstant c in
          FStar_Format.text uu____1287
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1304 =
            match uu____1304 with
            | (name,p) ->
                let uu____1309 =
                  let uu____1311 =
                    let uu____1312 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1312 in
                  let uu____1314 =
                    let uu____1316 =
                      let uu____1318 = doc_of_pattern currentModule p in
                      [uu____1318] in
                    (FStar_Format.text "=") :: uu____1316 in
                  uu____1311 :: uu____1314 in
                FStar_Format.reduce1 uu____1309 in
          let uu____1319 =
            let uu____1320 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1320 in
          FStar_Format.cbrackets uu____1319
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1327 = is_standard_constructor ctor in
            if uu____1327
            then
              let uu____1328 =
                let uu____1331 = as_standard_constructor ctor in
                FStar_Option.get uu____1331 in
              snd uu____1328
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1343 = is_standard_constructor ctor in
            if uu____1343
            then
              let uu____1344 =
                let uu____1347 = as_standard_constructor ctor in
                FStar_Option.get uu____1347 in
              snd uu____1344
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1359 =
                  let uu____1361 =
                    let uu____1362 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1362 in
                  let uu____1363 =
                    let uu____1365 =
                      let uu____1367 = doc_of_pattern currentModule xs in
                      [uu____1367] in
                    (FStar_Format.text "::") :: uu____1365 in
                  uu____1361 :: uu____1363 in
                FStar_Format.reduce uu____1359
            | (uu____1368,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1369)::[]) ->
                let uu____1372 =
                  let uu____1374 =
                    let uu____1376 =
                      let uu____1377 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1377 in
                    [uu____1376] in
                  (FStar_Format.text name) :: uu____1374 in
                FStar_Format.reduce1 uu____1372
            | uu____1378 ->
                let uu____1382 =
                  let uu____1384 =
                    let uu____1386 =
                      let uu____1387 =
                        let uu____1388 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1388 in
                      FStar_Format.parens uu____1387 in
                    [uu____1386] in
                  (FStar_Format.text name) :: uu____1384 in
                FStar_Format.reduce1 uu____1382 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1396 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1396
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1404  ->
      match uu____1404 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1411 =
                  let uu____1413 =
                    let uu____1415 = doc_of_pattern currentModule p in
                    [uu____1415] in
                  (FStar_Format.text "|") :: uu____1413 in
                FStar_Format.reduce1 uu____1411
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1420 =
                  let uu____1422 =
                    let uu____1424 = doc_of_pattern currentModule p in
                    [uu____1424; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1422 in
                FStar_Format.reduce1 uu____1420 in
          let uu____1425 =
            let uu____1427 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1428 =
              let uu____1430 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1430; FStar_Format.text "end"] in
            uu____1427 :: uu____1428 in
          FStar_Format.combine FStar_Format.hardline uu____1425
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1434  ->
      match uu____1434 with
      | (rec_,top_level,lets) ->
          let for1 uu____1447 =
            match uu____1447 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1450;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ids1 =
                  FStar_List.map
                    (fun uu____1467  ->
                       match uu____1467 with
                       | (x,uu____1471) -> FStar_Format.text x) ids in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1474 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1474
                     then
                       match tys with
                       | Some (uu____1475::uu____1476,uu____1477) ->
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
                          | Some (uu____1492::uu____1493,uu____1494) ->
                              FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1509 =
                  let uu____1511 =
                    let uu____1512 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1512 in
                  let uu____1513 =
                    let uu____1515 = FStar_Format.reduce1 ids1 in
                    [uu____1515; ty_annot; FStar_Format.text "="; e1] in
                  uu____1511 :: uu____1513 in
                FStar_Format.reduce1 uu____1509 in
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
  fun uu____1525  ->
    match uu____1525 with
    | (lineno,file) ->
        let uu____1528 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1528
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
      let for1 uu____1548 =
        match uu____1548 with
        | (uu____1557,x,mangle_opt,tparams,body) ->
            let x1 = match mangle_opt with | None  -> x | Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1572 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1572
              | uu____1573 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1578 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1578) tparams in
                  let uu____1579 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1579 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1596 =
                    match uu____1596 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1605 =
                    let uu____1606 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1606 in
                  FStar_Format.cbrackets uu____1605
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1621 =
                    match uu____1621 with
                    | (name,tys) ->
                        (match tys with
                         | [] -> FStar_Format.text name
                         | uu____1629 ->
                             let tys1 =
                               FStar_List.map
                                 (doc_of_mltype currentModule
                                    (t_prio_tpl, Left)) tys in
                             let tys2 =
                               FStar_Format.combine (FStar_Format.text " * ")
                                 tys1 in
                             FStar_Format.reduce1
                               [FStar_Format.text name;
                               FStar_Format.text "of";
                               tys2]) in
                  let ctors1 = FStar_List.map forctor ctors in
                  let ctors2 =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors1 in
                  FStar_Format.combine FStar_Format.hardline ctors2 in
            let doc1 =
              let uu____1645 =
                let uu____1647 =
                  let uu____1649 =
                    let uu____1650 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1650 in
                  [uu____1649] in
                tparams1 :: uu____1647 in
              FStar_Format.reduce1 uu____1645 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1654 =
                   let uu____1656 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1656; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1654) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1671 =
            let uu____1673 =
              let uu____1675 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1675] in
            (FStar_Format.text "type") :: uu____1673 in
          FStar_Format.reduce1 uu____1671
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
          let uu____1691 =
            let uu____1693 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1694 =
              let uu____1696 = doc_of_sig currentModule subsig in
              let uu____1697 =
                let uu____1699 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1699] in
              uu____1696 :: uu____1697 in
            uu____1693 :: uu____1694 in
          FStar_Format.combine FStar_Format.hardline uu____1691
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1711 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1711 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1713,ty)) ->
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
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1745 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1745 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1748,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1754 =
            let uu____1756 =
              let uu____1758 =
                let uu____1760 =
                  let uu____1762 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1762] in
                (FStar_Format.text "=") :: uu____1760 in
              (FStar_Format.text "_") :: uu____1758 in
            (FStar_Format.text "let") :: uu____1756 in
          FStar_Format.reduce1 uu____1754
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1778 ->
                  FStar_Format.empty
              | uu____1779 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1785  ->
    match uu____1785 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1823 =
          match uu____1823 with
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
                  (fun uu____1862  ->
                     match uu____1862 with
                     | (s,uu____1866) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1881 =
                let uu____1883 =
                  let uu____1885 =
                    let uu____1887 = FStar_Format.reduce sub3 in
                    [uu____1887;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1885 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1883 in
              FStar_Format.reduce uu____1881
        and for1_mod istop uu____1890 =
          match uu____1890 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1927 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____1934 =
                  let uu____1936 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____1936
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
                FStar_Format.reduce1 uu____1934 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1947  ->
                     match uu____1947 with
                     | (uu____1950,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____1968 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____1968
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____1971 =
                let uu____1973 =
                  let uu____1975 =
                    let uu____1977 =
                      let uu____1979 =
                        let uu____1981 =
                          let uu____1983 = FStar_Format.reduce sub3 in
                          [uu____1983;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____1981 in
                      FStar_Format.hardline :: uu____1979 in
                    FStar_List.append maybe_open_pervasives uu____1977 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____1975 in
                FStar_List.append prefix1 uu____1973 in
              FStar_All.pipe_left FStar_Format.reduce uu____1971 in
        let docs1 =
          FStar_List.map
            (fun uu____2001  ->
               match uu____2001 with
               | (x,s,m) ->
                   let uu____2028 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2029 = for1_mod true (x, s, m) in
                   (uu____2028, uu____2029)) mllib in
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
        let uu____2049 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2049 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2059 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2059 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1