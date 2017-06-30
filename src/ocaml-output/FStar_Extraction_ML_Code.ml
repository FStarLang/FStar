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
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
let t_prio_fun: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10"), (Infix Right))
let t_prio_tpl: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix NonAssoc))
let t_prio_name: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), Postfix)
let e_bin_prio_lambda: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "5"), Prefix)
let e_bin_prio_if: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "15"), Prefix)
let e_bin_prio_letin: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "19"), Prefix)
let e_bin_prio_or: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix Left))
let e_bin_prio_and: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "25"), (Infix Left))
let e_bin_prio_eq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "27"), (Infix NonAssoc))
let e_bin_prio_order: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "29"), (Infix NonAssoc))
let e_bin_prio_op1: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), (Infix Left))
let e_bin_prio_op2: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "40"), (Infix Left))
let e_bin_prio_op3: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "50"), (Infix Left))
let e_bin_prio_op4: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "60"), (Infix Left))
let e_bin_prio_comb: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "70"), (Infix Left))
let e_bin_prio_seq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "100"), (Infix Left))
let e_app_prio: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10000"), (Infix Left))
let min_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let max_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  (FStar_Util.max_int, (Infix NonAssoc))
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
                  let uu____181 = FStar_Util.first_N cg_len ns in
                  match uu____181 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____201 =
                           let uu____203 =
                             let uu____205 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____205] in
                           FStar_List.append pfx uu____203 in
                         FStar_Pervasives_Native.Some uu____201
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None) in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____224 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____224 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____227 ->
          let uu____228 = x in
          (match uu____228 with
           | (ns,x1) ->
               let uu____233 = path_of_ns currentModule ns in (uu____233, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____240 =
      let uu____241 =
        let uu____242 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____242 in
      let uu____243 = FStar_String.get s (Prims.parse_int "0") in
      uu____241 <> uu____243 in
    if uu____240 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____256 = mlpath_of_mlpath currentModule mlp in
         match uu____256 with
         | (p,s) ->
             let uu____261 =
               let uu____263 =
                 let uu____265 = ptsym_of_symbol s in [uu____265] in
               FStar_List.append p uu____263 in
             FStar_String.concat "." uu____261)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____274 = mlpath_of_mlpath currentModule mlp in
      match uu____274 with
      | (p,s) ->
          let s1 =
            let uu____280 =
              let uu____281 =
                let uu____282 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____282 in
              let uu____283 = FStar_String.get s (Prims.parse_int "0") in
              uu____281 <> uu____283 in
            if uu____280 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s1])
let infix_prim_ops:
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list
  =
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
let prim_uni_ops:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")]
let prim_types uu____409 = []
let prim_constructors:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option
  =
  fun uu____439  ->
    match uu____439 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____465  ->
               match uu____465 with | (y,uu____472,uu____473) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____488 = as_bin_op p in uu____488 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____512  ->
    match uu____512 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____528  -> match uu____528 with | (y,uu____532) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____540 = as_uni_op p in uu____540 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____559  ->
    match uu____559 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____575  -> match uu____575 with | (y,uu____579) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____587 = as_standard_constructor p in
    uu____587 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____611  ->
    fun inner  ->
      fun doc1  ->
        match uu____611 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____644 = _inner in
              match uu____644 with
              | (pi,fi) ->
                  let uu____649 = _outer in
                  (match uu____649 with
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
                           | (uu____654,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____655,uu____656) -> false))) in
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
    fun uu___118_676  ->
      match uu___118_676 with
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
        let uu____696 =
          let uu____697 = escape_or escape_char_hex c in
          Prims.strcat uu____697 "'" in
        Prims.strcat "'" uu____696
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____711,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____718,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____733 =
          let uu____734 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____734 "\"" in
        Prims.strcat "\"" uu____733
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____736 =
          let uu____737 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____737 "\"" in
        Prims.strcat "\"" uu____736
    | uu____738 ->
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
            let uu____760 =
              let uu____761 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____761 in
            FStar_Format.text uu____760
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____769 =
                let uu____770 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____770 in
              FStar_Format.parens uu____769 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____779 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____785 =
                    let uu____786 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____786 in
                  FStar_Format.parens uu____785 in
            let name1 = ptsym currentModule name in
            let uu____788 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____788
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____790,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____798 =
              let uu____799 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____799 in
            maybe_paren outer t_prio_fun uu____798
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____800 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____800
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____805 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____805
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
            let uu____853 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____853
            then
              let uu____854 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____854
            else
              (let uu____856 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____856)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____867 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____867
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____869 = string_of_mlconstant c in
            FStar_Format.text uu____869
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____871) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____873 = ptsym currentModule path in
            FStar_Format.text uu____873
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____889 =
              match uu____889 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____897 =
                    let uu____899 =
                      let uu____900 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____900 in
                    [uu____899; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____897 in
            let uu____902 =
              let uu____903 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____903 in
            FStar_Format.cbrackets uu____902
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____910 = is_standard_constructor ctor in
              if uu____910
              then
                let uu____911 =
                  let uu____914 = as_standard_constructor ctor in
                  FStar_Option.get uu____914 in
                FStar_Pervasives_Native.snd uu____911
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____926 = is_standard_constructor ctor in
              if uu____926
              then
                let uu____927 =
                  let uu____930 = as_standard_constructor ctor in
                  FStar_Option.get uu____930 in
                FStar_Pervasives_Native.snd uu____927
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____946,uu____947) ->
                  let uu____950 =
                    let uu____952 =
                      let uu____954 =
                        let uu____955 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____955 in
                      [uu____954] in
                    (FStar_Format.text name) :: uu____952 in
                  FStar_Format.reduce1 uu____950 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____963 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____963) es in
            let docs2 =
              let uu____967 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____967 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____969,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____979 =
                  let uu____981 =
                    let uu____983 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____983] in
                  FStar_Format.hardline :: uu____981 in
                FStar_Format.reduce uu____979
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____990 =
              let uu____991 =
                let uu____993 =
                  let uu____995 =
                    let uu____997 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____997] in
                  doc1 :: uu____995 in
                pre :: uu____993 in
              FStar_Format.combine FStar_Format.hardline uu____991 in
            FStar_Format.parens uu____990
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1004::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1006;
                    FStar_Extraction_ML_Syntax.loc = uu____1007;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1009)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1011;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1012;_}::[])
                 when
                 let uu____1030 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1030 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1043;
                            FStar_Extraction_ML_Syntax.loc = uu____1044;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1046;
                       FStar_Extraction_ML_Syntax.loc = uu____1047;_} when
                       let uu____1058 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1059 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1058 = uu____1059 -> branches
                   | e2 ->
                       [(FStar_Extraction_ML_Syntax.MLP_Wild,
                          FStar_Pervasives_Native.None, e2)] in
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1080;
                   FStar_Extraction_ML_Syntax.loc = uu____1081;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1091;
                   FStar_Extraction_ML_Syntax.loc = uu____1092;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1097 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1108 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1108)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1115 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1115
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1118 =
                   let uu____1120 =
                     let uu____1122 =
                       let uu____1124 =
                         let uu____1125 = ptsym currentModule f in
                         FStar_Format.text uu____1125 in
                       [uu____1124] in
                     (FStar_Format.text ".") :: uu____1122 in
                   e2 :: uu____1120 in
                 FStar_Format.reduce uu____1118) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1143 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1143
              then
                let uu____1144 =
                  let uu____1146 =
                    let uu____1148 =
                      let uu____1150 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1152 =
                              let uu____1154 =
                                let uu____1156 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1156] in
                              (FStar_Format.text " : ") :: uu____1154 in
                            FStar_Format.reduce1 uu____1152
                        | uu____1157 -> FStar_Format.text "" in
                      [uu____1150; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1148 in
                  (FStar_Format.text "(") :: uu____1146 in
                FStar_Format.reduce1 uu____1144
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1170  ->
                   match uu____1170 with
                   | ((x,uu____1176),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1184 =
                let uu____1186 =
                  let uu____1188 = FStar_Format.reduce1 ids1 in
                  [uu____1188; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1186 in
              FStar_Format.reduce1 uu____1184 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1196 =
                let uu____1198 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1199 =
                  let uu____1201 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1201; FStar_Format.text "end"] in
                uu____1198 :: uu____1199 in
              FStar_Format.combine FStar_Format.hardline uu____1196 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1212 =
                let uu____1214 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1215 =
                  let uu____1217 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1220 =
                    let uu____1222 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1223 =
                      let uu____1225 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1225; FStar_Format.text "end"] in
                    uu____1222 :: uu____1223 in
                  uu____1217 :: uu____1220 in
                uu____1214 :: uu____1215 in
              FStar_Format.combine FStar_Format.hardline uu____1212 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1247 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1247 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1251 =
              let uu____1253 =
                let uu____1255 =
                  let uu____1256 = ptctor currentModule exn in
                  FStar_Format.text uu____1256 in
                [uu____1255] in
              (FStar_Format.text "raise") :: uu____1253 in
            FStar_Format.reduce1 uu____1251
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1265 =
              let uu____1267 =
                let uu____1269 =
                  let uu____1270 = ptctor currentModule exn in
                  FStar_Format.text uu____1270 in
                let uu____1271 =
                  let uu____1273 =
                    let uu____1274 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1274 in
                  [uu____1273] in
                uu____1269 :: uu____1271 in
              (FStar_Format.text "raise") :: uu____1267 in
            FStar_Format.reduce1 uu____1265
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1287 =
              let uu____1289 =
                let uu____1291 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1294 =
                  let uu____1296 =
                    let uu____1298 =
                      let uu____1299 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1299 in
                    [uu____1298] in
                  (FStar_Format.text "with") :: uu____1296 in
                uu____1291 :: uu____1294 in
              (FStar_Format.text "try") :: uu____1289 in
            FStar_Format.combine FStar_Format.hardline uu____1287
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
          let uu____1305 =
            let uu____1311 = as_bin_op p in FStar_Option.get uu____1311 in
          match uu____1305 with
          | (uu____1323,prio,txt) ->
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
        let uu____1340 =
          let uu____1343 = as_uni_op p in FStar_Option.get uu____1343 in
        match uu____1340 with
        | (uu____1349,txt) ->
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
          let uu____1358 = string_of_mlconstant c in
          FStar_Format.text uu____1358
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1375 =
            match uu____1375 with
            | (name,p) ->
                let uu____1380 =
                  let uu____1382 =
                    let uu____1383 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1383 in
                  let uu____1385 =
                    let uu____1387 =
                      let uu____1389 = doc_of_pattern currentModule p in
                      [uu____1389] in
                    (FStar_Format.text "=") :: uu____1387 in
                  uu____1382 :: uu____1385 in
                FStar_Format.reduce1 uu____1380 in
          let uu____1390 =
            let uu____1391 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1391 in
          FStar_Format.cbrackets uu____1390
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1398 = is_standard_constructor ctor in
            if uu____1398
            then
              let uu____1399 =
                let uu____1402 = as_standard_constructor ctor in
                FStar_Option.get uu____1402 in
              FStar_Pervasives_Native.snd uu____1399
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1414 = is_standard_constructor ctor in
            if uu____1414
            then
              let uu____1415 =
                let uu____1418 = as_standard_constructor ctor in
                FStar_Option.get uu____1418 in
              FStar_Pervasives_Native.snd uu____1415
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1430 =
                  let uu____1432 =
                    let uu____1433 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1433 in
                  let uu____1434 =
                    let uu____1436 =
                      let uu____1438 = doc_of_pattern currentModule xs in
                      [uu____1438] in
                    (FStar_Format.text "::") :: uu____1436 in
                  uu____1432 :: uu____1434 in
                FStar_Format.reduce uu____1430
            | (uu____1439,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1440)::[]) ->
                let uu____1443 =
                  let uu____1445 =
                    let uu____1447 =
                      let uu____1448 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1448 in
                    [uu____1447] in
                  (FStar_Format.text name) :: uu____1445 in
                FStar_Format.reduce1 uu____1443
            | uu____1449 ->
                let uu____1453 =
                  let uu____1455 =
                    let uu____1457 =
                      let uu____1458 =
                        let uu____1459 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1459 in
                      FStar_Format.parens uu____1458 in
                    [uu____1457] in
                  (FStar_Format.text name) :: uu____1455 in
                FStar_Format.reduce1 uu____1453 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1467 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1467
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1475  ->
      match uu____1475 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____1482 =
                  let uu____1484 =
                    let uu____1486 = doc_of_pattern currentModule p in
                    [uu____1486] in
                  (FStar_Format.text "|") :: uu____1484 in
                FStar_Format.reduce1 uu____1482
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1491 =
                  let uu____1493 =
                    let uu____1495 = doc_of_pattern currentModule p in
                    [uu____1495; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1493 in
                FStar_Format.reduce1 uu____1491 in
          let uu____1496 =
            let uu____1498 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1499 =
              let uu____1501 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1501; FStar_Format.text "end"] in
            uu____1498 :: uu____1499 in
          FStar_Format.combine FStar_Format.hardline uu____1496
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1505  ->
      match uu____1505 with
      | (rec_,top_level,lets) ->
          let for1 uu____1518 =
            match uu____1518 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1521;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1532 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1532
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____1533::uu____1534,uu____1535) ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.None  ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some
                              (uu____1550::uu____1551,uu____1552) ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1567 =
                  let uu____1569 =
                    let uu____1570 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1570 in
                  let uu____1571 =
                    let uu____1573 = FStar_Format.reduce1 ids in
                    [uu____1573; ty_annot; FStar_Format.text "="; e1] in
                  uu____1569 :: uu____1571 in
                FStar_Format.reduce1 uu____1567 in
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
  fun uu____1585  ->
    match uu____1585 with
    | (lineno,file) ->
        let uu____1588 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1588
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
      let for1 uu____1611 =
        match uu____1611 with
        | (uu____1621,x,mangle_opt,tparams,uu____1625,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1637 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1637
              | uu____1638 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1645 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1645) tparams in
                  let uu____1646 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1646 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1663 =
                    match uu____1663 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1672 =
                    let uu____1673 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1673 in
                  FStar_Format.cbrackets uu____1672
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1692 =
                    match uu____1692 with
                    | (name,tys) ->
                        let uu____1706 = FStar_List.split tys in
                        (match uu____1706 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1717 ->
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
              let uu____1736 =
                let uu____1738 =
                  let uu____1740 =
                    let uu____1741 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1741 in
                  [uu____1740] in
                tparams1 :: uu____1738 in
              FStar_Format.reduce1 uu____1736 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1745 =
                   let uu____1747 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1747; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1745) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1766 =
            let uu____1768 =
              let uu____1770 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1770] in
            (FStar_Format.text "type") :: uu____1768 in
          FStar_Format.reduce1 uu____1766
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
          let uu____1786 =
            let uu____1788 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1789 =
              let uu____1791 = doc_of_sig currentModule subsig in
              let uu____1792 =
                let uu____1794 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1794] in
              uu____1791 :: uu____1792 in
            uu____1788 :: uu____1789 in
          FStar_Format.combine FStar_Format.hardline uu____1786
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1806 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1806 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1808,ty)) ->
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
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1 in
          let args3 =
            let uu____1855 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1855 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1858,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1864 =
            let uu____1866 =
              let uu____1868 =
                let uu____1870 =
                  let uu____1872 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1872] in
                (FStar_Format.text "=") :: uu____1870 in
              (FStar_Format.text "_") :: uu____1868 in
            (FStar_Format.text "let") :: uu____1866 in
          FStar_Format.reduce1 uu____1864
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1893 ->
                  FStar_Format.empty
              | uu____1894 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1901  ->
    match uu____1901 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1939 =
          match uu____1939 with
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
                  (fun uu____1981  ->
                     match uu____1981 with
                     | (s,uu____1985) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____2001 =
                let uu____2003 =
                  let uu____2005 =
                    let uu____2007 = FStar_Format.reduce sub3 in
                    [uu____2007;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____2005 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____2003 in
              FStar_Format.reduce uu____2001
        and for1_mod istop uu____2010 =
          match uu____2010 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____2047 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____2054 =
                  let uu____2056 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____2056
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
                FStar_Format.reduce1 uu____2054 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____2070  ->
                     match uu____2070 with
                     | (uu____2073,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____2092 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____2092
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____2095 =
                let uu____2097 =
                  let uu____2099 =
                    let uu____2101 =
                      let uu____2103 =
                        let uu____2105 =
                          let uu____2107 = FStar_Format.reduce sub3 in
                          [uu____2107;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2105 in
                      FStar_Format.hardline :: uu____2103 in
                    FStar_List.append maybe_open_pervasives uu____2101 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____2099 in
                FStar_List.append prefix1 uu____2097 in
              FStar_All.pipe_left FStar_Format.reduce uu____2095 in
        let docs1 =
          FStar_List.map
            (fun uu____2131  ->
               match uu____2131 with
               | (x,s,m) ->
                   let uu____2158 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2159 = for1_mod true (x, s, m) in
                   (uu____2158, uu____2159)) mllib in
        docs1
let doc_of_mllib:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib
let string_of_mlexpr:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2182 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2182 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2194 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2194 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1