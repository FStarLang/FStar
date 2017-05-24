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
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some (_,FStar_Const.Int8 ))
      |FStar_Extraction_ML_Syntax.MLC_Int (s,Some (_,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____669 =
          let uu____670 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____670 "\"" in
        Prims.strcat "\"" uu____669
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____672 =
          let uu____673 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____673 "\"" in
        Prims.strcat "\"" uu____672
    | uu____674 ->
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
            let uu____696 =
              let uu____697 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____697 in
            FStar_Format.text uu____696
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____705 =
                let uu____706 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____706 in
              FStar_Format.parens uu____705 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____715 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____721 =
                    let uu____722 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____722 in
                  FStar_Format.parens uu____721 in
            let name1 = ptsym currentModule name in
            let uu____724 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____724
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____726,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____734 =
              let uu____735 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____735 in
            maybe_paren outer t_prio_fun uu____734
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____736 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____736
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
            let uu____788 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____788
            then
              let uu____789 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____789
            else
              (let uu____791 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____791)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____801 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____801
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____803 = string_of_mlconstant c in
            FStar_Format.text uu____803
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____805) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____807 = ptsym currentModule path in
            FStar_Format.text uu____807
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____823 =
              match uu____823 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____831 =
                    let uu____833 =
                      let uu____834 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____834 in
                    [uu____833; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____831 in
            let uu____836 =
              let uu____837 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____837 in
            FStar_Format.cbrackets uu____836
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____844 = is_standard_constructor ctor in
              if uu____844
              then
                let uu____845 =
                  let uu____848 = as_standard_constructor ctor in
                  FStar_Option.get uu____848 in
                snd uu____845
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____860 = is_standard_constructor ctor in
              if uu____860
              then
                let uu____861 =
                  let uu____864 = as_standard_constructor ctor in
                  FStar_Option.get uu____864 in
                snd uu____861
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____880,uu____881) ->
                  let uu____884 =
                    let uu____886 =
                      let uu____888 =
                        let uu____889 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____889 in
                      [uu____888] in
                    (FStar_Format.text name) :: uu____886 in
                  FStar_Format.reduce1 uu____884 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____895 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____895) es in
            let docs2 =
              let uu____899 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____899 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____901,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____911 =
                  let uu____913 =
                    let uu____915 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____915] in
                  FStar_Format.hardline :: uu____913 in
                FStar_Format.reduce uu____911
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____922 =
              let uu____923 =
                let uu____925 =
                  let uu____927 =
                    let uu____929 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____929] in
                  doc1 :: uu____927 in
                pre :: uu____925 in
              FStar_Format.combine FStar_Format.hardline uu____923 in
            FStar_Format.parens uu____922
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____936::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____938;
                    FStar_Extraction_ML_Syntax.loc = uu____939;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____941)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____943;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____944;_}::[])
                 when
                 let uu____962 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____962 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____975;
                            FStar_Extraction_ML_Syntax.loc = uu____976;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____978;
                       FStar_Extraction_ML_Syntax.loc = uu____979;_} when
                       let uu____990 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____991 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____990 = uu____991 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1012;
                   FStar_Extraction_ML_Syntax.loc = uu____1013;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1023;
                   FStar_Extraction_ML_Syntax.loc = uu____1024;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1029 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1040 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1040)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1047 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1047
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1050 =
                   let uu____1052 =
                     let uu____1054 =
                       let uu____1056 =
                         let uu____1057 = ptsym currentModule f in
                         FStar_Format.text uu____1057 in
                       [uu____1056] in
                     (FStar_Format.text ".") :: uu____1054 in
                   e2 :: uu____1052 in
                 FStar_Format.reduce uu____1050) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1075 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1075
              then
                let uu____1076 =
                  let uu____1078 =
                    let uu____1080 =
                      let uu____1082 =
                        match xt with
                        | Some xxt ->
                            let uu____1084 =
                              let uu____1086 =
                                let uu____1088 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1088] in
                              (FStar_Format.text " : ") :: uu____1086 in
                            FStar_Format.reduce1 uu____1084
                        | uu____1089 -> FStar_Format.text "" in
                      [uu____1082; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1080 in
                  (FStar_Format.text "(") :: uu____1078 in
                FStar_Format.reduce1 uu____1076
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1098  ->
                   match uu____1098 with
                   | ((x,uu____1104),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1112 =
                let uu____1114 =
                  let uu____1116 = FStar_Format.reduce1 ids1 in
                  [uu____1116; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1114 in
              FStar_Format.reduce1 uu____1112 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1124 =
                let uu____1126 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1127 =
                  let uu____1129 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1129; FStar_Format.text "end"] in
                uu____1126 :: uu____1127 in
              FStar_Format.combine FStar_Format.hardline uu____1124 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1140 =
                let uu____1142 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1143 =
                  let uu____1145 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1148 =
                    let uu____1150 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1151 =
                      let uu____1153 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1153; FStar_Format.text "end"] in
                    uu____1150 :: uu____1151 in
                  uu____1145 :: uu____1148 in
                uu____1142 :: uu____1143 in
              FStar_Format.combine FStar_Format.hardline uu____1140 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1175 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1175 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1179 =
              let uu____1181 =
                let uu____1183 =
                  let uu____1184 = ptctor currentModule exn in
                  FStar_Format.text uu____1184 in
                [uu____1183] in
              (FStar_Format.text "raise") :: uu____1181 in
            FStar_Format.reduce1 uu____1179
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1193 =
              let uu____1195 =
                let uu____1197 =
                  let uu____1198 = ptctor currentModule exn in
                  FStar_Format.text uu____1198 in
                let uu____1199 =
                  let uu____1201 =
                    let uu____1202 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1202 in
                  [uu____1201] in
                uu____1197 :: uu____1199 in
              (FStar_Format.text "raise") :: uu____1195 in
            FStar_Format.reduce1 uu____1193
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1215 =
              let uu____1217 =
                let uu____1219 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1222 =
                  let uu____1224 =
                    let uu____1226 =
                      let uu____1227 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1227 in
                    [uu____1226] in
                  (FStar_Format.text "with") :: uu____1224 in
                uu____1219 :: uu____1222 in
              (FStar_Format.text "try") :: uu____1217 in
            FStar_Format.combine FStar_Format.hardline uu____1215
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
          let uu____1233 =
            let uu____1239 = as_bin_op p in FStar_Option.get uu____1239 in
          match uu____1233 with
          | (uu____1251,prio,txt) ->
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
        let uu____1268 =
          let uu____1271 = as_uni_op p in FStar_Option.get uu____1271 in
        match uu____1268 with
        | (uu____1277,txt) ->
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
          let uu____1286 = string_of_mlconstant c in
          FStar_Format.text uu____1286
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1303 =
            match uu____1303 with
            | (name,p) ->
                let uu____1308 =
                  let uu____1310 =
                    let uu____1311 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1311 in
                  let uu____1313 =
                    let uu____1315 =
                      let uu____1317 = doc_of_pattern currentModule p in
                      [uu____1317] in
                    (FStar_Format.text "=") :: uu____1315 in
                  uu____1310 :: uu____1313 in
                FStar_Format.reduce1 uu____1308 in
          let uu____1318 =
            let uu____1319 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1319 in
          FStar_Format.cbrackets uu____1318
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1326 = is_standard_constructor ctor in
            if uu____1326
            then
              let uu____1327 =
                let uu____1330 = as_standard_constructor ctor in
                FStar_Option.get uu____1330 in
              snd uu____1327
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1342 = is_standard_constructor ctor in
            if uu____1342
            then
              let uu____1343 =
                let uu____1346 = as_standard_constructor ctor in
                FStar_Option.get uu____1346 in
              snd uu____1343
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1358 =
                  let uu____1360 =
                    let uu____1361 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1361 in
                  let uu____1362 =
                    let uu____1364 =
                      let uu____1366 = doc_of_pattern currentModule xs in
                      [uu____1366] in
                    (FStar_Format.text "::") :: uu____1364 in
                  uu____1360 :: uu____1362 in
                FStar_Format.reduce uu____1358
            | (uu____1367,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1368)::[]) ->
                let uu____1371 =
                  let uu____1373 =
                    let uu____1375 =
                      let uu____1376 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1376 in
                    [uu____1375] in
                  (FStar_Format.text name) :: uu____1373 in
                FStar_Format.reduce1 uu____1371
            | uu____1377 ->
                let uu____1381 =
                  let uu____1383 =
                    let uu____1385 =
                      let uu____1386 =
                        let uu____1387 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1387 in
                      FStar_Format.parens uu____1386 in
                    [uu____1385] in
                  (FStar_Format.text name) :: uu____1383 in
                FStar_Format.reduce1 uu____1381 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1395 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1395
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1403  ->
      match uu____1403 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1410 =
                  let uu____1412 =
                    let uu____1414 = doc_of_pattern currentModule p in
                    [uu____1414] in
                  (FStar_Format.text "|") :: uu____1412 in
                FStar_Format.reduce1 uu____1410
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1419 =
                  let uu____1421 =
                    let uu____1423 = doc_of_pattern currentModule p in
                    [uu____1423; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1421 in
                FStar_Format.reduce1 uu____1419 in
          let uu____1424 =
            let uu____1426 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1427 =
              let uu____1429 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1429; FStar_Format.text "end"] in
            uu____1426 :: uu____1427 in
          FStar_Format.combine FStar_Format.hardline uu____1424
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1433  ->
      match uu____1433 with
      | (rec_,top_level,lets) ->
          let for1 uu____1446 =
            match uu____1446 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1449;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ids1 =
                  FStar_List.map
                    (fun uu____1466  ->
                       match uu____1466 with
                       | (x,uu____1470) -> FStar_Format.text x) ids in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1473 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1473
                     then
                       match tys with
                       | Some (_::_,_)|None  -> FStar_Format.text ""
                       | Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | None |Some (_::_,_) -> FStar_Format.text ""
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
                    let uu____1512 = FStar_Format.reduce1 ids1 in
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
                  let forctor uu____1618 =
                    match uu____1618 with
                    | (name,tys) ->
                        (match tys with
                         | [] -> FStar_Format.text name
                         | uu____1626 ->
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
              let uu____1642 =
                let uu____1644 =
                  let uu____1646 =
                    let uu____1647 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1647 in
                  [uu____1646] in
                tparams1 :: uu____1644 in
              FStar_Format.reduce1 uu____1642 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1651 =
                   let uu____1653 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1653; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1651) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1668 =
            let uu____1670 =
              let uu____1672 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1672] in
            (FStar_Format.text "type") :: uu____1670 in
          FStar_Format.reduce1 uu____1668
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
          let uu____1688 =
            let uu____1690 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1691 =
              let uu____1693 = doc_of_sig currentModule subsig in
              let uu____1694 =
                let uu____1696 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1696] in
              uu____1693 :: uu____1694 in
            uu____1690 :: uu____1691 in
          FStar_Format.combine FStar_Format.hardline uu____1688
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1708 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1708 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1710,ty)) ->
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
            let uu____1742 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1742 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1745,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1751 =
            let uu____1753 =
              let uu____1755 =
                let uu____1757 =
                  let uu____1759 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1759] in
                (FStar_Format.text "=") :: uu____1757 in
              (FStar_Format.text "_") :: uu____1755 in
            (FStar_Format.text "let") :: uu____1753 in
          FStar_Format.reduce1 uu____1751
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1775 ->
                  FStar_Format.empty
              | uu____1776 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1782  ->
    match uu____1782 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1820 =
          match uu____1820 with
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
                  (fun uu____1859  ->
                     match uu____1859 with
                     | (s,uu____1863) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1878 =
                let uu____1880 =
                  let uu____1882 =
                    let uu____1884 = FStar_Format.reduce sub3 in
                    [uu____1884;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1882 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1880 in
              FStar_Format.reduce uu____1878
        and for1_mod istop uu____1887 =
          match uu____1887 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1924 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____1931 =
                  let uu____1933 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____1933
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
                FStar_Format.reduce1 uu____1931 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1944  ->
                     match uu____1944 with
                     | (uu____1947,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____1965 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____1965
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____1968 =
                let uu____1970 =
                  let uu____1972 =
                    let uu____1974 =
                      let uu____1976 =
                        let uu____1978 =
                          let uu____1980 = FStar_Format.reduce sub3 in
                          [uu____1980;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____1978 in
                      FStar_Format.hardline :: uu____1976 in
                    FStar_List.append maybe_open_pervasives uu____1974 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____1972 in
                FStar_List.append prefix1 uu____1970 in
              FStar_All.pipe_left FStar_Format.reduce uu____1968 in
        let docs1 =
          FStar_List.map
            (fun uu____1998  ->
               match uu____1998 with
               | (x,s,m) ->
                   let uu____2025 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2026 = for1_mod true (x, s, m) in
                   (uu____2025, uu____2026)) mllib in
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
        let uu____2046 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2046 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2056 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2056 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1