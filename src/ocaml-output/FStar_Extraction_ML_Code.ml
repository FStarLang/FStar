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
                  let uu____161 = FStar_Util.first_N cg_len ns in
                  match uu____161 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____181 =
                           let uu____183 =
                             let uu____185 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____185] in
                           FStar_List.append pfx uu____183 in
                         Some uu____181
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____202 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____202 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____205 ->
          let uu____206 = x in
          (match uu____206 with
           | (ns,x1) ->
               let uu____211 = path_of_ns currentModule ns in (uu____211, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____217 =
      let uu____218 =
        let uu____219 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____219 in
      let uu____220 = FStar_String.get s (Prims.parse_int "0") in
      uu____218 <> uu____220 in
    if uu____217 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (fst mlp)
      then ptsym_of_symbol (snd mlp)
      else
        (let uu____231 = mlpath_of_mlpath currentModule mlp in
         match uu____231 with
         | (p,s) ->
             let uu____236 =
               let uu____238 =
                 let uu____240 = ptsym_of_symbol s in [uu____240] in
               FStar_List.append p uu____238 in
             FStar_String.concat "." uu____236)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____247 = mlpath_of_mlpath currentModule mlp in
      match uu____247 with
      | (p,s) ->
          let s1 =
            let uu____253 =
              let uu____254 =
                let uu____255 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____255 in
              let uu____256 = FStar_String.get s (Prims.parse_int "0") in
              uu____254 <> uu____256 in
            if uu____253 then Prims.strcat "U__" s else s in
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
let prim_types uu____381 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      option
  =
  fun uu____409  ->
    match uu____409 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____431  ->
               match uu____431 with | (y,uu____438,uu____439) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____453 = as_bin_op p in uu____453 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____476  ->
    match uu____476 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____489  -> match uu____489 with | (y,uu____493) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____500 = as_uni_op p in uu____500 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____517  ->
    match uu____517 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____530  -> match uu____530 with | (y,uu____534) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let uu____541 = as_standard_constructor p in uu____541 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____562  ->
    fun inner  ->
      fun doc1  ->
        match uu____562 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____595 = _inner in
              match uu____595 with
              | (pi,fi) ->
                  let uu____600 = _outer in
                  (match uu____600 with
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
                           | (uu____605,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____606,uu____607) -> false))) in
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
    fun uu___118_623  ->
      match uu___118_623 with
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
        let uu____642 =
          let uu____643 = escape_or escape_char_hex c in
          Prims.strcat uu____643 "'" in
        Prims.strcat "'" uu____642
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int32 )) ->
        Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int64 )) ->
        Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____657,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____664,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____679 =
          let uu____680 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____680 "\"" in
        Prims.strcat "\"" uu____679
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____682 =
          let uu____683 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____683 "\"" in
        Prims.strcat "\"" uu____682
    | uu____684 ->
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
            let uu____706 =
              let uu____707 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____707 in
            FStar_Format.text uu____706
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____715 =
                let uu____716 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____716 in
              FStar_Format.parens uu____715 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____725 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____731 =
                    let uu____732 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____732 in
                  FStar_Format.parens uu____731 in
            let name1 = ptsym currentModule name in
            let uu____734 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____734
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____736,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____744 =
              let uu____745 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____745 in
            maybe_paren outer t_prio_fun uu____744
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____746 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____746
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
            let uu____798 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____798
            then
              let uu____799 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____799
            else
              (let uu____801 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____801)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____811 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____811
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____813 = string_of_mlconstant c in
            FStar_Format.text uu____813
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____815) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____817 = ptsym currentModule path in
            FStar_Format.text uu____817
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____833 =
              match uu____833 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____841 =
                    let uu____843 =
                      let uu____844 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____844 in
                    [uu____843; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____841 in
            let uu____846 =
              let uu____847 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____847 in
            FStar_Format.cbrackets uu____846
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____854 = is_standard_constructor ctor in
              if uu____854
              then
                let uu____855 =
                  let uu____858 = as_standard_constructor ctor in
                  FStar_Option.get uu____858 in
                snd uu____855
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____870 = is_standard_constructor ctor in
              if uu____870
              then
                let uu____871 =
                  let uu____874 = as_standard_constructor ctor in
                  FStar_Option.get uu____874 in
                snd uu____871
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____890,uu____891) ->
                  let uu____894 =
                    let uu____896 =
                      let uu____898 =
                        let uu____899 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____899 in
                      [uu____898] in
                    (FStar_Format.text name) :: uu____896 in
                  FStar_Format.reduce1 uu____894 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____905 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____905) es in
            let docs2 =
              let uu____909 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____909 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____911,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____921 =
                  let uu____923 =
                    let uu____925 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____925] in
                  FStar_Format.hardline :: uu____923 in
                FStar_Format.reduce uu____921
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____932 =
              let uu____933 =
                let uu____935 =
                  let uu____937 =
                    let uu____939 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____939] in
                  doc1 :: uu____937 in
                pre :: uu____935 in
              FStar_Format.combine FStar_Format.hardline uu____933 in
            FStar_Format.parens uu____932
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____946::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____948;
                    FStar_Extraction_ML_Syntax.loc = uu____949;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____951)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____953;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____954;_}::[])
                 when
                 let uu____972 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____972 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____985;
                            FStar_Extraction_ML_Syntax.loc = uu____986;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____988;
                       FStar_Extraction_ML_Syntax.loc = uu____989;_} when
                       let uu____1000 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1001 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1000 = uu____1001 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1022;
                   FStar_Extraction_ML_Syntax.loc = uu____1023;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1033;
                   FStar_Extraction_ML_Syntax.loc = uu____1034;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1039 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1050 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1050)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1057 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1057
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1060 =
                   let uu____1062 =
                     let uu____1064 =
                       let uu____1066 =
                         let uu____1067 = ptsym currentModule f in
                         FStar_Format.text uu____1067 in
                       [uu____1066] in
                     (FStar_Format.text ".") :: uu____1064 in
                   e2 :: uu____1062 in
                 FStar_Format.reduce uu____1060) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1085 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1085
              then
                let uu____1086 =
                  let uu____1088 =
                    let uu____1090 =
                      let uu____1092 =
                        match xt with
                        | Some xxt ->
                            let uu____1094 =
                              let uu____1096 =
                                let uu____1098 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1098] in
                              (FStar_Format.text " : ") :: uu____1096 in
                            FStar_Format.reduce1 uu____1094
                        | uu____1099 -> FStar_Format.text "" in
                      [uu____1092; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1090 in
                  (FStar_Format.text "(") :: uu____1088 in
                FStar_Format.reduce1 uu____1086
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1108  ->
                   match uu____1108 with
                   | ((x,uu____1114),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1122 =
                let uu____1124 =
                  let uu____1126 = FStar_Format.reduce1 ids1 in
                  [uu____1126; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1124 in
              FStar_Format.reduce1 uu____1122 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1134 =
                let uu____1136 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1137 =
                  let uu____1139 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1139; FStar_Format.text "end"] in
                uu____1136 :: uu____1137 in
              FStar_Format.combine FStar_Format.hardline uu____1134 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1150 =
                let uu____1152 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1153 =
                  let uu____1155 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1158 =
                    let uu____1160 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1161 =
                      let uu____1163 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1163; FStar_Format.text "end"] in
                    uu____1160 :: uu____1161 in
                  uu____1155 :: uu____1158 in
                uu____1152 :: uu____1153 in
              FStar_Format.combine FStar_Format.hardline uu____1150 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1185 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1185 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1189 =
              let uu____1191 =
                let uu____1193 =
                  let uu____1194 = ptctor currentModule exn in
                  FStar_Format.text uu____1194 in
                [uu____1193] in
              (FStar_Format.text "raise") :: uu____1191 in
            FStar_Format.reduce1 uu____1189
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1203 =
              let uu____1205 =
                let uu____1207 =
                  let uu____1208 = ptctor currentModule exn in
                  FStar_Format.text uu____1208 in
                let uu____1209 =
                  let uu____1211 =
                    let uu____1212 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1212 in
                  [uu____1211] in
                uu____1207 :: uu____1209 in
              (FStar_Format.text "raise") :: uu____1205 in
            FStar_Format.reduce1 uu____1203
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1225 =
              let uu____1227 =
                let uu____1229 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1232 =
                  let uu____1234 =
                    let uu____1236 =
                      let uu____1237 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1237 in
                    [uu____1236] in
                  (FStar_Format.text "with") :: uu____1234 in
                uu____1229 :: uu____1232 in
              (FStar_Format.text "try") :: uu____1227 in
            FStar_Format.combine FStar_Format.hardline uu____1225
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
          let uu____1243 =
            let uu____1249 = as_bin_op p in FStar_Option.get uu____1249 in
          match uu____1243 with
          | (uu____1261,prio,txt) ->
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
        let uu____1278 =
          let uu____1281 = as_uni_op p in FStar_Option.get uu____1281 in
        match uu____1278 with
        | (uu____1287,txt) ->
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
          let uu____1296 = string_of_mlconstant c in
          FStar_Format.text uu____1296
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1313 =
            match uu____1313 with
            | (name,p) ->
                let uu____1318 =
                  let uu____1320 =
                    let uu____1321 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1321 in
                  let uu____1323 =
                    let uu____1325 =
                      let uu____1327 = doc_of_pattern currentModule p in
                      [uu____1327] in
                    (FStar_Format.text "=") :: uu____1325 in
                  uu____1320 :: uu____1323 in
                FStar_Format.reduce1 uu____1318 in
          let uu____1328 =
            let uu____1329 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1329 in
          FStar_Format.cbrackets uu____1328
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1336 = is_standard_constructor ctor in
            if uu____1336
            then
              let uu____1337 =
                let uu____1340 = as_standard_constructor ctor in
                FStar_Option.get uu____1340 in
              snd uu____1337
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1352 = is_standard_constructor ctor in
            if uu____1352
            then
              let uu____1353 =
                let uu____1356 = as_standard_constructor ctor in
                FStar_Option.get uu____1356 in
              snd uu____1353
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1368 =
                  let uu____1370 =
                    let uu____1371 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1371 in
                  let uu____1372 =
                    let uu____1374 =
                      let uu____1376 = doc_of_pattern currentModule xs in
                      [uu____1376] in
                    (FStar_Format.text "::") :: uu____1374 in
                  uu____1370 :: uu____1372 in
                FStar_Format.reduce uu____1368
            | (uu____1377,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1378)::[]) ->
                let uu____1381 =
                  let uu____1383 =
                    let uu____1385 =
                      let uu____1386 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1386 in
                    [uu____1385] in
                  (FStar_Format.text name) :: uu____1383 in
                FStar_Format.reduce1 uu____1381
            | uu____1387 ->
                let uu____1391 =
                  let uu____1393 =
                    let uu____1395 =
                      let uu____1396 =
                        let uu____1397 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1397 in
                      FStar_Format.parens uu____1396 in
                    [uu____1395] in
                  (FStar_Format.text name) :: uu____1393 in
                FStar_Format.reduce1 uu____1391 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1405 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1405
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1413  ->
      match uu____1413 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1420 =
                  let uu____1422 =
                    let uu____1424 = doc_of_pattern currentModule p in
                    [uu____1424] in
                  (FStar_Format.text "|") :: uu____1422 in
                FStar_Format.reduce1 uu____1420
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1429 =
                  let uu____1431 =
                    let uu____1433 = doc_of_pattern currentModule p in
                    [uu____1433; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1431 in
                FStar_Format.reduce1 uu____1429 in
          let uu____1434 =
            let uu____1436 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1437 =
              let uu____1439 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1439; FStar_Format.text "end"] in
            uu____1436 :: uu____1437 in
          FStar_Format.combine FStar_Format.hardline uu____1434
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1443  ->
      match uu____1443 with
      | (rec_,top_level,lets) ->
          let for1 uu____1456 =
            match uu____1456 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1459;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ids1 =
                  FStar_List.map
                    (fun uu____1476  ->
                       match uu____1476 with
                       | (x,uu____1480) -> FStar_Format.text x) ids in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1483 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1483
                     then
                       match tys with
                       | Some (uu____1484::uu____1485,uu____1486) ->
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
                          | Some (uu____1501::uu____1502,uu____1503) ->
                              FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1518 =
                  let uu____1520 =
                    let uu____1521 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1521 in
                  let uu____1522 =
                    let uu____1524 = FStar_Format.reduce1 ids1 in
                    [uu____1524; ty_annot; FStar_Format.text "="; e1] in
                  uu____1520 :: uu____1522 in
                FStar_Format.reduce1 uu____1518 in
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
  fun uu____1534  ->
    match uu____1534 with
    | (lineno,file) ->
        let uu____1537 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1537
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
      let for1 uu____1557 =
        match uu____1557 with
        | (uu____1566,x,mangle_opt,tparams,body) ->
            let x1 = match mangle_opt with | None  -> x | Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1581 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1581
              | uu____1582 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1587 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1587) tparams in
                  let uu____1588 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1588 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1605 =
                    match uu____1605 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1614 =
                    let uu____1615 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1615 in
                  FStar_Format.cbrackets uu____1614
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1630 =
                    match uu____1630 with
                    | (name,tys) ->
                        (match tys with
                         | [] -> FStar_Format.text name
                         | uu____1638 ->
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
              let uu____1654 =
                let uu____1656 =
                  let uu____1658 =
                    let uu____1659 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1659 in
                  [uu____1658] in
                tparams1 :: uu____1656 in
              FStar_Format.reduce1 uu____1654 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1663 =
                   let uu____1665 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1665; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1663) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1683 =
            let uu____1685 =
              let uu____1687 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1687] in
            (FStar_Format.text "type") :: uu____1685 in
          FStar_Format.reduce1 uu____1683
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
          let uu____1703 =
            let uu____1705 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1706 =
              let uu____1708 = doc_of_sig currentModule subsig in
              let uu____1709 =
                let uu____1711 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1711] in
              uu____1708 :: uu____1709 in
            uu____1705 :: uu____1706 in
          FStar_Format.combine FStar_Format.hardline uu____1703
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1723 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1723 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1725,ty)) ->
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
            let uu____1757 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1757 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1760,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1766 =
            let uu____1768 =
              let uu____1770 =
                let uu____1772 =
                  let uu____1774 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1774] in
                (FStar_Format.text "=") :: uu____1772 in
              (FStar_Format.text "_") :: uu____1770 in
            (FStar_Format.text "let") :: uu____1768 in
          FStar_Format.reduce1 uu____1766
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1790 ->
                  FStar_Format.empty
              | uu____1791 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1797  ->
    match uu____1797 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1835 =
          match uu____1835 with
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
                  (fun uu____1874  ->
                     match uu____1874 with
                     | (s,uu____1878) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1893 =
                let uu____1895 =
                  let uu____1897 =
                    let uu____1899 = FStar_Format.reduce sub3 in
                    [uu____1899;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1897 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1895 in
              FStar_Format.reduce uu____1893
        and for1_mod istop uu____1902 =
          match uu____1902 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1939 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____1946 =
                  let uu____1948 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____1948
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
                FStar_Format.reduce1 uu____1946 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1959  ->
                     match uu____1959 with
                     | (uu____1962,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____1980 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____1980
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____1983 =
                let uu____1985 =
                  let uu____1987 =
                    let uu____1989 =
                      let uu____1991 =
                        let uu____1993 =
                          let uu____1995 = FStar_Format.reduce sub3 in
                          [uu____1995;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____1993 in
                      FStar_Format.hardline :: uu____1991 in
                    FStar_List.append maybe_open_pervasives uu____1989 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____1987 in
                FStar_List.append prefix1 uu____1985 in
              FStar_All.pipe_left FStar_Format.reduce uu____1983 in
        let docs1 =
          FStar_List.map
            (fun uu____2013  ->
               match uu____2013 with
               | (x,s,m) ->
                   let uu____2040 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2041 = for1_mod true (x, s, m) in
                   (uu____2040, uu____2041)) mllib in
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
        let uu____2061 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2061 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2071 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2071 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1