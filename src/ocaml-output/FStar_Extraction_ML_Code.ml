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
  | ([],uu____114) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____128,uu____129) -> false
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
                  let uu____182 = FStar_Util.first_N cg_len ns in
                  match uu____182 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____202 =
                           let uu____204 =
                             let uu____206 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____206] in
                           FStar_List.append pfx uu____204 in
                         FStar_Pervasives_Native.Some uu____202
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
      let uu____225 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____225 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____228 ->
          let uu____229 = x in
          (match uu____229 with
           | (ns,x1) ->
               let uu____234 = path_of_ns currentModule ns in (uu____234, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____241 =
      let uu____242 =
        let uu____243 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____243 in
      let uu____244 = FStar_String.get s (Prims.parse_int "0") in
      uu____242 <> uu____244 in
    if uu____241 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____257 = mlpath_of_mlpath currentModule mlp in
         match uu____257 with
         | (p,s) ->
             let uu____262 =
               let uu____264 =
                 let uu____266 = ptsym_of_symbol s in [uu____266] in
               FStar_List.append p uu____264 in
             FStar_String.concat "." uu____262)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____275 = mlpath_of_mlpath currentModule mlp in
      match uu____275 with
      | (p,s) ->
          let s1 =
            let uu____281 =
              let uu____282 =
                let uu____283 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____283 in
              let uu____284 = FStar_String.get s (Prims.parse_int "0") in
              uu____282 <> uu____284 in
            if uu____281 then Prims.strcat "U__" s else s in
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
let prim_types uu____410 = []
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
  fun uu____440  ->
    match uu____440 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____466  ->
               match uu____466 with | (y,uu____473,uu____474) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____489 = as_bin_op p in uu____489 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____513  ->
    match uu____513 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____529  -> match uu____529 with | (y,uu____533) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____541 = as_uni_op p in uu____541 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____560  ->
    match uu____560 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____576  -> match uu____576 with | (y,uu____580) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____588 = as_standard_constructor p in
    uu____588 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____612  ->
    fun inner  ->
      fun doc1  ->
        match uu____612 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____645 = _inner in
              match uu____645 with
              | (pi,fi) ->
                  let uu____650 = _outer in
                  (match uu____650 with
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
                           | (uu____655,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____656,uu____657) -> false))) in
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
    fun uu___118_677  ->
      match uu___118_677 with
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
        let uu____697 =
          let uu____698 = escape_or escape_char_hex c in
          Prims.strcat uu____698 "'" in
        Prims.strcat "'" uu____697
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____712,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____719,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____734 =
          let uu____735 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____735 "\"" in
        Prims.strcat "\"" uu____734
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____737 =
          let uu____738 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____738 "\"" in
        Prims.strcat "\"" uu____737
    | uu____739 ->
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
            let uu____761 =
              let uu____762 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____762 in
            FStar_Format.text uu____761
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____770 =
                let uu____771 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____771 in
              FStar_Format.parens uu____770 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____780 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____786 =
                    let uu____787 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____787 in
                  FStar_Format.parens uu____786 in
            let name1 = ptsym currentModule name in
            let uu____789 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____789
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____791,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____799 =
              let uu____800 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____800 in
            maybe_paren outer t_prio_fun uu____799
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____801 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____801
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____806 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____806
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
            let uu____854 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____854
            then
              let uu____855 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____855
            else
              (let uu____857 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____857)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____868 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____868
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____870 = string_of_mlconstant c in
            FStar_Format.text uu____870
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____872) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____874 = ptsym currentModule path in
            FStar_Format.text uu____874
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____890 =
              match uu____890 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____898 =
                    let uu____900 =
                      let uu____901 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____901 in
                    [uu____900; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____898 in
            let uu____903 =
              let uu____904 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____904 in
            FStar_Format.cbrackets uu____903
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____911 = is_standard_constructor ctor in
              if uu____911
              then
                let uu____912 =
                  let uu____915 = as_standard_constructor ctor in
                  FStar_Option.get uu____915 in
                FStar_Pervasives_Native.snd uu____912
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____927 = is_standard_constructor ctor in
              if uu____927
              then
                let uu____928 =
                  let uu____931 = as_standard_constructor ctor in
                  FStar_Option.get uu____931 in
                FStar_Pervasives_Native.snd uu____928
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____947,uu____948) ->
                  let uu____951 =
                    let uu____953 =
                      let uu____955 =
                        let uu____956 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____956 in
                      [uu____955] in
                    (FStar_Format.text name) :: uu____953 in
                  FStar_Format.reduce1 uu____951 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____964 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____964) es in
            let docs2 =
              let uu____968 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____968 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____970,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____980 =
                  let uu____982 =
                    let uu____984 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____984] in
                  FStar_Format.hardline :: uu____982 in
                FStar_Format.reduce uu____980
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____991 =
              let uu____992 =
                let uu____994 =
                  let uu____996 =
                    let uu____998 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____998] in
                  doc1 :: uu____996 in
                pre :: uu____994 in
              FStar_Format.combine FStar_Format.hardline uu____992 in
            FStar_Format.parens uu____991
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1005::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1007;
                    FStar_Extraction_ML_Syntax.loc = uu____1008;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1010)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1012;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1013;_}::[])
                 when
                 let uu____1031 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1031 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1044;
                            FStar_Extraction_ML_Syntax.loc = uu____1045;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1047;
                       FStar_Extraction_ML_Syntax.loc = uu____1048;_} when
                       let uu____1059 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1060 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1059 = uu____1060 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1081;
                   FStar_Extraction_ML_Syntax.loc = uu____1082;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1092;
                   FStar_Extraction_ML_Syntax.loc = uu____1093;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1098 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1109 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1109)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1116 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1116
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1119 =
                   let uu____1121 =
                     let uu____1123 =
                       let uu____1125 =
                         let uu____1126 = ptsym currentModule f in
                         FStar_Format.text uu____1126 in
                       [uu____1125] in
                     (FStar_Format.text ".") :: uu____1123 in
                   e2 :: uu____1121 in
                 FStar_Format.reduce uu____1119) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1144 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1144
              then
                let uu____1145 =
                  let uu____1147 =
                    let uu____1149 =
                      let uu____1151 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1153 =
                              let uu____1155 =
                                let uu____1157 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1157] in
                              (FStar_Format.text " : ") :: uu____1155 in
                            FStar_Format.reduce1 uu____1153
                        | uu____1158 -> FStar_Format.text "" in
                      [uu____1151; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1149 in
                  (FStar_Format.text "(") :: uu____1147 in
                FStar_Format.reduce1 uu____1145
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1171  ->
                   match uu____1171 with
                   | ((x,uu____1177),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1185 =
                let uu____1187 =
                  let uu____1189 = FStar_Format.reduce1 ids1 in
                  [uu____1189; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1187 in
              FStar_Format.reduce1 uu____1185 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1197 =
                let uu____1199 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1200 =
                  let uu____1202 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1202; FStar_Format.text "end"] in
                uu____1199 :: uu____1200 in
              FStar_Format.combine FStar_Format.hardline uu____1197 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1213 =
                let uu____1215 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1216 =
                  let uu____1218 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1221 =
                    let uu____1223 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1224 =
                      let uu____1226 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1226; FStar_Format.text "end"] in
                    uu____1223 :: uu____1224 in
                  uu____1218 :: uu____1221 in
                uu____1215 :: uu____1216 in
              FStar_Format.combine FStar_Format.hardline uu____1213 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1248 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1248 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1252 =
              let uu____1254 =
                let uu____1256 =
                  let uu____1257 = ptctor currentModule exn in
                  FStar_Format.text uu____1257 in
                [uu____1256] in
              (FStar_Format.text "raise") :: uu____1254 in
            FStar_Format.reduce1 uu____1252
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1266 =
              let uu____1268 =
                let uu____1270 =
                  let uu____1271 = ptctor currentModule exn in
                  FStar_Format.text uu____1271 in
                let uu____1272 =
                  let uu____1274 =
                    let uu____1275 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1275 in
                  [uu____1274] in
                uu____1270 :: uu____1272 in
              (FStar_Format.text "raise") :: uu____1268 in
            FStar_Format.reduce1 uu____1266
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1288 =
              let uu____1290 =
                let uu____1292 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1295 =
                  let uu____1297 =
                    let uu____1299 =
                      let uu____1300 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1300 in
                    [uu____1299] in
                  (FStar_Format.text "with") :: uu____1297 in
                uu____1292 :: uu____1295 in
              (FStar_Format.text "try") :: uu____1290 in
            FStar_Format.combine FStar_Format.hardline uu____1288
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
          let uu____1306 =
            let uu____1312 = as_bin_op p in FStar_Option.get uu____1312 in
          match uu____1306 with
          | (uu____1324,prio,txt) ->
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
        let uu____1341 =
          let uu____1344 = as_uni_op p in FStar_Option.get uu____1344 in
        match uu____1341 with
        | (uu____1350,txt) ->
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
          let uu____1359 = string_of_mlconstant c in
          FStar_Format.text uu____1359
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1376 =
            match uu____1376 with
            | (name,p) ->
                let uu____1381 =
                  let uu____1383 =
                    let uu____1384 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1384 in
                  let uu____1386 =
                    let uu____1388 =
                      let uu____1390 = doc_of_pattern currentModule p in
                      [uu____1390] in
                    (FStar_Format.text "=") :: uu____1388 in
                  uu____1383 :: uu____1386 in
                FStar_Format.reduce1 uu____1381 in
          let uu____1391 =
            let uu____1392 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1392 in
          FStar_Format.cbrackets uu____1391
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1399 = is_standard_constructor ctor in
            if uu____1399
            then
              let uu____1400 =
                let uu____1403 = as_standard_constructor ctor in
                FStar_Option.get uu____1403 in
              FStar_Pervasives_Native.snd uu____1400
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1415 = is_standard_constructor ctor in
            if uu____1415
            then
              let uu____1416 =
                let uu____1419 = as_standard_constructor ctor in
                FStar_Option.get uu____1419 in
              FStar_Pervasives_Native.snd uu____1416
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1431 =
                  let uu____1433 =
                    let uu____1434 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1434 in
                  let uu____1435 =
                    let uu____1437 =
                      let uu____1439 = doc_of_pattern currentModule xs in
                      [uu____1439] in
                    (FStar_Format.text "::") :: uu____1437 in
                  uu____1433 :: uu____1435 in
                FStar_Format.reduce uu____1431
            | (uu____1440,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1441)::[]) ->
                let uu____1444 =
                  let uu____1446 =
                    let uu____1448 =
                      let uu____1449 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1449 in
                    [uu____1448] in
                  (FStar_Format.text name) :: uu____1446 in
                FStar_Format.reduce1 uu____1444
            | uu____1450 ->
                let uu____1454 =
                  let uu____1456 =
                    let uu____1458 =
                      let uu____1459 =
                        let uu____1460 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1460 in
                      FStar_Format.parens uu____1459 in
                    [uu____1458] in
                  (FStar_Format.text name) :: uu____1456 in
                FStar_Format.reduce1 uu____1454 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1468 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1468
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1476  ->
      match uu____1476 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____1483 =
                  let uu____1485 =
                    let uu____1487 = doc_of_pattern currentModule p in
                    [uu____1487] in
                  (FStar_Format.text "|") :: uu____1485 in
                FStar_Format.reduce1 uu____1483
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1492 =
                  let uu____1494 =
                    let uu____1496 = doc_of_pattern currentModule p in
                    [uu____1496; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1494 in
                FStar_Format.reduce1 uu____1492 in
          let uu____1497 =
            let uu____1499 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1500 =
              let uu____1502 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1502; FStar_Format.text "end"] in
            uu____1499 :: uu____1500 in
          FStar_Format.combine FStar_Format.hardline uu____1497
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1506  ->
      match uu____1506 with
      | (rec_,top_level,lets) ->
          let for1 uu____1519 =
            match uu____1519 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1522;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1533 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1533
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____1534::uu____1535,uu____1536) ->
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
                              (uu____1551::uu____1552,uu____1553) ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1568 =
                  let uu____1570 =
                    let uu____1571 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1571 in
                  let uu____1572 =
                    let uu____1574 = FStar_Format.reduce1 ids in
                    [uu____1574; ty_annot; FStar_Format.text "="; e1] in
                  uu____1570 :: uu____1572 in
                FStar_Format.reduce1 uu____1568 in
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
  fun uu____1586  ->
    match uu____1586 with
    | (lineno,file) ->
        let uu____1589 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1589
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
      let for1 uu____1612 =
        match uu____1612 with
        | (uu____1622,x,mangle_opt,tparams,uu____1626,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1638 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1638
              | uu____1639 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1646 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1646) tparams in
                  let uu____1647 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1647 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1664 =
                    match uu____1664 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1673 =
                    let uu____1674 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1674 in
                  FStar_Format.cbrackets uu____1673
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1693 =
                    match uu____1693 with
                    | (name,tys) ->
                        let uu____1707 = FStar_List.split tys in
                        (match uu____1707 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1718 ->
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
              let uu____1737 =
                let uu____1739 =
                  let uu____1741 =
                    let uu____1742 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1742 in
                  [uu____1741] in
                tparams1 :: uu____1739 in
              FStar_Format.reduce1 uu____1737 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1746 =
                   let uu____1748 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1748; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1746) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1767 =
            let uu____1769 =
              let uu____1771 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1771] in
            (FStar_Format.text "type") :: uu____1769 in
          FStar_Format.reduce1 uu____1767
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
          let uu____1787 =
            let uu____1789 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1790 =
              let uu____1792 = doc_of_sig currentModule subsig in
              let uu____1793 =
                let uu____1795 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1795] in
              uu____1792 :: uu____1793 in
            uu____1789 :: uu____1790 in
          FStar_Format.combine FStar_Format.hardline uu____1787
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1807 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1807 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1809,ty)) ->
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
            let uu____1856 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1856 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1859,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1865 =
            let uu____1867 =
              let uu____1869 =
                let uu____1871 =
                  let uu____1873 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1873] in
                (FStar_Format.text "=") :: uu____1871 in
              (FStar_Format.text "_") :: uu____1869 in
            (FStar_Format.text "let") :: uu____1867 in
          FStar_Format.reduce1 uu____1865
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1894 ->
                  FStar_Format.empty
              | uu____1895 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1902  ->
    match uu____1902 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1940 =
          match uu____1940 with
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
                  (fun uu____1982  ->
                     match uu____1982 with
                     | (s,uu____1986) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____2002 =
                let uu____2004 =
                  let uu____2006 =
                    let uu____2008 = FStar_Format.reduce sub3 in
                    [uu____2008;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____2006 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____2004 in
              FStar_Format.reduce uu____2002
        and for1_mod istop uu____2011 =
          match uu____2011 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____2048 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____2055 =
                  let uu____2057 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____2057
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
                FStar_Format.reduce1 uu____2055 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____2071  ->
                     match uu____2071 with
                     | (uu____2074,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____2093 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____2093
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____2096 =
                let uu____2098 =
                  let uu____2100 =
                    let uu____2102 =
                      let uu____2104 =
                        let uu____2106 =
                          let uu____2108 = FStar_Format.reduce sub3 in
                          [uu____2108;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2106 in
                      FStar_Format.hardline :: uu____2104 in
                    FStar_List.append maybe_open_pervasives uu____2102 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____2100 in
                FStar_List.append prefix1 uu____2098 in
              FStar_All.pipe_left FStar_Format.reduce uu____2096 in
        let docs1 =
          FStar_List.map
            (fun uu____2132  ->
               match uu____2132 with
               | (x,s,m) ->
                   let uu____2159 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2160 = for1_mod true (x, s, m) in
                   (uu____2159, uu____2160)) mllib in
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
        let uu____2183 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2183 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2195 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2195 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1