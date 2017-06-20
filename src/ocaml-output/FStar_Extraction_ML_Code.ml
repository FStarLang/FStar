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
                  let uu____161 = FStar_Util.first_N cg_len ns in
                  match uu____161 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____179 =
                           let uu____181 =
                             let uu____183 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____183] in
                           FStar_List.append pfx uu____181 in
                         Some uu____179
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____200 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____200 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____203 ->
          let uu____204 = x in
          (match uu____204 with
           | (ns,x1) ->
               let uu____209 = path_of_ns currentModule ns in (uu____209, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____215 =
      let uu____216 =
        let uu____217 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____217 in
      let uu____218 = FStar_String.get s (Prims.parse_int "0") in
      uu____216 <> uu____218 in
    if uu____215 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (fst mlp)
      then ptsym_of_symbol (snd mlp)
      else
        (let uu____229 = mlpath_of_mlpath currentModule mlp in
         match uu____229 with
         | (p,s) ->
             let uu____234 =
               let uu____236 =
                 let uu____238 = ptsym_of_symbol s in [uu____238] in
               FStar_List.append p uu____236 in
             FStar_String.concat "." uu____234)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____245 = mlpath_of_mlpath currentModule mlp in
      match uu____245 with
      | (p,s) ->
          let s1 =
            let uu____251 =
              let uu____252 =
                let uu____253 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____253 in
              let uu____254 = FStar_String.get s (Prims.parse_int "0") in
              uu____252 <> uu____254 in
            if uu____251 then Prims.strcat "U__" s else s in
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
let prim_types uu____379 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      option
  =
  fun uu____407  ->
    match uu____407 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____433  ->
               match uu____433 with | (y,uu____440,uu____441) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____455 = as_bin_op p in uu____455 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____478  ->
    match uu____478 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____494  -> match uu____494 with | (y,uu____498) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let uu____505 = as_uni_op p in uu____505 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) option
  =
  fun uu____522  ->
    match uu____522 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____538  -> match uu____538 with | (y,uu____542) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let uu____549 = as_standard_constructor p in uu____549 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____570  ->
    fun inner  ->
      fun doc1  ->
        match uu____570 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____603 = _inner in
              match uu____603 with
              | (pi,fi) ->
                  let uu____608 = _outer in
                  (match uu____608 with
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
                           | (uu____613,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____614,uu____615) -> false))) in
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
    fun uu___117_631  ->
      match uu___117_631 with
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
        let uu____650 =
          let uu____651 = escape_or escape_char_hex c in
          Prims.strcat uu____651 "'" in
        Prims.strcat "'" uu____650
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int32 )) ->
        Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (FStar_Const.Signed ,FStar_Const.Int64 )) ->
        Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____665,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,Some (uu____672,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____687 =
          let uu____688 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____688 "\"" in
        Prims.strcat "\"" uu____687
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____690 =
          let uu____691 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____691 "\"" in
        Prims.strcat "\"" uu____690
    | uu____692 ->
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
            let uu____714 =
              let uu____715 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____715 in
            FStar_Format.text uu____714
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____723 =
                let uu____724 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____724 in
              FStar_Format.parens uu____723 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____733 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____739 =
                    let uu____740 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____740 in
                  FStar_Format.parens uu____739 in
            let name1 = ptsym currentModule name in
            let uu____742 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____742
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____744,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____752 =
              let uu____753 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____753 in
            maybe_paren outer t_prio_fun uu____752
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____754 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____754
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
            let uu____806 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____806
            then
              let uu____807 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____807
            else
              (let uu____809 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____809)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____820 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____820
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____822 = string_of_mlconstant c in
            FStar_Format.text uu____822
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____824) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____826 = ptsym currentModule path in
            FStar_Format.text uu____826
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____842 =
              match uu____842 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____850 =
                    let uu____852 =
                      let uu____853 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____853 in
                    [uu____852; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____850 in
            let uu____855 =
              let uu____856 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____856 in
            FStar_Format.cbrackets uu____855
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____863 = is_standard_constructor ctor in
              if uu____863
              then
                let uu____864 =
                  let uu____867 = as_standard_constructor ctor in
                  FStar_Option.get uu____867 in
                snd uu____864
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____879 = is_standard_constructor ctor in
              if uu____879
              then
                let uu____880 =
                  let uu____883 = as_standard_constructor ctor in
                  FStar_Option.get uu____883 in
                snd uu____880
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____899,uu____900) ->
                  let uu____903 =
                    let uu____905 =
                      let uu____907 =
                        let uu____908 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____908 in
                      [uu____907] in
                    (FStar_Format.text name) :: uu____905 in
                  FStar_Format.reduce1 uu____903 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____916 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____916) es in
            let docs2 =
              let uu____920 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____920 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____922,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____932 =
                  let uu____934 =
                    let uu____936 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____936] in
                  FStar_Format.hardline :: uu____934 in
                FStar_Format.reduce uu____932
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____943 =
              let uu____944 =
                let uu____946 =
                  let uu____948 =
                    let uu____950 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____950] in
                  doc1 :: uu____948 in
                pre :: uu____946 in
              FStar_Format.combine FStar_Format.hardline uu____944 in
            FStar_Format.parens uu____943
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____957::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____959;
                    FStar_Extraction_ML_Syntax.loc = uu____960;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____962)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____964;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____965;_}::[])
                 when
                 let uu____983 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____983 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____996;
                            FStar_Extraction_ML_Syntax.loc = uu____997;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____999;
                       FStar_Extraction_ML_Syntax.loc = uu____1000;_} when
                       let uu____1011 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1012 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1011 = uu____1012 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1033;
                   FStar_Extraction_ML_Syntax.loc = uu____1034;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1044;
                   FStar_Extraction_ML_Syntax.loc = uu____1045;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1050 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1061 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1061)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1068 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1068
              then
                FStar_Format.reduce
                  [e2; FStar_Format.text "."; FStar_Format.text (snd f)]
              else
                (let uu____1071 =
                   let uu____1073 =
                     let uu____1075 =
                       let uu____1077 =
                         let uu____1078 = ptsym currentModule f in
                         FStar_Format.text uu____1078 in
                       [uu____1077] in
                     (FStar_Format.text ".") :: uu____1075 in
                   e2 :: uu____1073 in
                 FStar_Format.reduce uu____1071) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1096 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1096
              then
                let uu____1097 =
                  let uu____1099 =
                    let uu____1101 =
                      let uu____1103 =
                        match xt with
                        | Some xxt ->
                            let uu____1105 =
                              let uu____1107 =
                                let uu____1109 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1109] in
                              (FStar_Format.text " : ") :: uu____1107 in
                            FStar_Format.reduce1 uu____1105
                        | uu____1110 -> FStar_Format.text "" in
                      [uu____1103; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1101 in
                  (FStar_Format.text "(") :: uu____1099 in
                FStar_Format.reduce1 uu____1097
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1123  ->
                   match uu____1123 with
                   | ((x,uu____1129),xt) -> bvar_annot x (Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1137 =
                let uu____1139 =
                  let uu____1141 = FStar_Format.reduce1 ids1 in
                  [uu____1141; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1139 in
              FStar_Format.reduce1 uu____1137 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1149 =
                let uu____1151 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1152 =
                  let uu____1154 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1154; FStar_Format.text "end"] in
                uu____1151 :: uu____1152 in
              FStar_Format.combine FStar_Format.hardline uu____1149 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1165 =
                let uu____1167 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1168 =
                  let uu____1170 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1173 =
                    let uu____1175 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1176 =
                      let uu____1178 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1178; FStar_Format.text "end"] in
                    uu____1175 :: uu____1176 in
                  uu____1170 :: uu____1173 in
                uu____1167 :: uu____1168 in
              FStar_Format.combine FStar_Format.hardline uu____1165 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1200 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1200 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1204 =
              let uu____1206 =
                let uu____1208 =
                  let uu____1209 = ptctor currentModule exn in
                  FStar_Format.text uu____1209 in
                [uu____1208] in
              (FStar_Format.text "raise") :: uu____1206 in
            FStar_Format.reduce1 uu____1204
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1218 =
              let uu____1220 =
                let uu____1222 =
                  let uu____1223 = ptctor currentModule exn in
                  FStar_Format.text uu____1223 in
                let uu____1224 =
                  let uu____1226 =
                    let uu____1227 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1227 in
                  [uu____1226] in
                uu____1222 :: uu____1224 in
              (FStar_Format.text "raise") :: uu____1220 in
            FStar_Format.reduce1 uu____1218
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1240 =
              let uu____1242 =
                let uu____1244 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1247 =
                  let uu____1249 =
                    let uu____1251 =
                      let uu____1252 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1252 in
                    [uu____1251] in
                  (FStar_Format.text "with") :: uu____1249 in
                uu____1244 :: uu____1247 in
              (FStar_Format.text "try") :: uu____1242 in
            FStar_Format.combine FStar_Format.hardline uu____1240
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
          let uu____1258 =
            let uu____1264 = as_bin_op p in FStar_Option.get uu____1264 in
          match uu____1258 with
          | (uu____1276,prio,txt) ->
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
        let uu____1293 =
          let uu____1296 = as_uni_op p in FStar_Option.get uu____1296 in
        match uu____1293 with
        | (uu____1302,txt) ->
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
          let uu____1311 = string_of_mlconstant c in
          FStar_Format.text uu____1311
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text (fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1328 =
            match uu____1328 with
            | (name,p) ->
                let uu____1333 =
                  let uu____1335 =
                    let uu____1336 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1336 in
                  let uu____1338 =
                    let uu____1340 =
                      let uu____1342 = doc_of_pattern currentModule p in
                      [uu____1342] in
                    (FStar_Format.text "=") :: uu____1340 in
                  uu____1335 :: uu____1338 in
                FStar_Format.reduce1 uu____1333 in
          let uu____1343 =
            let uu____1344 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1344 in
          FStar_Format.cbrackets uu____1343
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1351 = is_standard_constructor ctor in
            if uu____1351
            then
              let uu____1352 =
                let uu____1355 = as_standard_constructor ctor in
                FStar_Option.get uu____1355 in
              snd uu____1352
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1367 = is_standard_constructor ctor in
            if uu____1367
            then
              let uu____1368 =
                let uu____1371 = as_standard_constructor ctor in
                FStar_Option.get uu____1371 in
              snd uu____1368
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1383 =
                  let uu____1385 =
                    let uu____1386 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1386 in
                  let uu____1387 =
                    let uu____1389 =
                      let uu____1391 = doc_of_pattern currentModule xs in
                      [uu____1391] in
                    (FStar_Format.text "::") :: uu____1389 in
                  uu____1385 :: uu____1387 in
                FStar_Format.reduce uu____1383
            | (uu____1392,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1393)::[]) ->
                let uu____1396 =
                  let uu____1398 =
                    let uu____1400 =
                      let uu____1401 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1401 in
                    [uu____1400] in
                  (FStar_Format.text name) :: uu____1398 in
                FStar_Format.reduce1 uu____1396
            | uu____1402 ->
                let uu____1406 =
                  let uu____1408 =
                    let uu____1410 =
                      let uu____1411 =
                        let uu____1412 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1412 in
                      FStar_Format.parens uu____1411 in
                    [uu____1410] in
                  (FStar_Format.text name) :: uu____1408 in
                FStar_Format.reduce1 uu____1406 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1420 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1420
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1428  ->
      match uu____1428 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                let uu____1435 =
                  let uu____1437 =
                    let uu____1439 = doc_of_pattern currentModule p in
                    [uu____1439] in
                  (FStar_Format.text "|") :: uu____1437 in
                FStar_Format.reduce1 uu____1435
            | Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1444 =
                  let uu____1446 =
                    let uu____1448 = doc_of_pattern currentModule p in
                    [uu____1448; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1446 in
                FStar_Format.reduce1 uu____1444 in
          let uu____1449 =
            let uu____1451 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1452 =
              let uu____1454 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1454; FStar_Format.text "end"] in
            uu____1451 :: uu____1452 in
          FStar_Format.combine FStar_Format.hardline uu____1449
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1458  ->
      match uu____1458 with
      | (rec_,top_level,lets) ->
          let for1 uu____1471 =
            match uu____1471 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1474;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1485 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1485
                     then
                       match tys with
                       | Some (uu____1486::uu____1487,uu____1488) ->
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
                          | Some (uu____1503::uu____1504,uu____1505) ->
                              FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1520 =
                  let uu____1522 =
                    let uu____1523 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1523 in
                  let uu____1524 =
                    let uu____1526 = FStar_Format.reduce1 ids in
                    [uu____1526; ty_annot; FStar_Format.text "="; e1] in
                  uu____1522 :: uu____1524 in
                FStar_Format.reduce1 uu____1520 in
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
  fun uu____1538  ->
    match uu____1538 with
    | (lineno,file) ->
        let uu____1541 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1541
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
      let for1 uu____1561 =
        match uu____1561 with
        | (uu____1570,x,mangle_opt,tparams,body) ->
            let x1 = match mangle_opt with | None  -> x | Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1585 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1585
              | uu____1586 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1593 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1593) tparams in
                  let uu____1594 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1594 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1611 =
                    match uu____1611 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1620 =
                    let uu____1621 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1621 in
                  FStar_Format.cbrackets uu____1620
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1640 =
                    match uu____1640 with
                    | (name,tys) ->
                        let uu____1654 = FStar_List.split tys in
                        (match uu____1654 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1665 ->
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
              let uu____1684 =
                let uu____1686 =
                  let uu____1688 =
                    let uu____1689 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1689 in
                  [uu____1688] in
                tparams1 :: uu____1686 in
              FStar_Format.reduce1 uu____1684 in
            (match body with
             | None  -> doc1
             | Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1693 =
                   let uu____1695 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1695; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1693) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1710 =
            let uu____1712 =
              let uu____1714 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1714] in
            (FStar_Format.text "type") :: uu____1712 in
          FStar_Format.reduce1 uu____1710
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
          let uu____1730 =
            let uu____1732 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1733 =
              let uu____1735 = doc_of_sig currentModule subsig in
              let uu____1736 =
                let uu____1738 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1738] in
              uu____1735 :: uu____1736 in
            uu____1732 :: uu____1733 in
          FStar_Format.combine FStar_Format.hardline uu____1730
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1750 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1750 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1752,ty)) ->
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
            let uu____1797 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1797 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1800,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1806 =
            let uu____1808 =
              let uu____1810 =
                let uu____1812 =
                  let uu____1814 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1814] in
                (FStar_Format.text "=") :: uu____1812 in
              (FStar_Format.text "_") :: uu____1810 in
            (FStar_Format.text "let") :: uu____1808 in
          FStar_Format.reduce1 uu____1806
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1833 ->
                  FStar_Format.empty
              | uu____1834 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1840  ->
    match uu____1840 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1878 =
          match uu____1878 with
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
                  (fun uu____1920  ->
                     match uu____1920 with
                     | (s,uu____1924) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1940 =
                let uu____1942 =
                  let uu____1944 =
                    let uu____1946 = FStar_Format.reduce sub3 in
                    [uu____1946;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | None  -> FStar_Format.empty
                   | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                    uu____1944 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1942 in
              FStar_Format.reduce uu____1940
        and for1_mod istop uu____1949 =
          match uu____1949 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1986 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____1993 =
                  let uu____1995 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____1995
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
                FStar_Format.reduce1 uu____1993 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____2009  ->
                     match uu____2009 with
                     | (uu____2012,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____2031 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____2031
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____2034 =
                let uu____2036 =
                  let uu____2038 =
                    let uu____2040 =
                      let uu____2042 =
                        let uu____2044 =
                          let uu____2046 = FStar_Format.reduce sub3 in
                          [uu____2046;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | None  -> FStar_Format.empty
                         | Some s -> FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2044 in
                      FStar_Format.hardline :: uu____2042 in
                    FStar_List.append maybe_open_pervasives uu____2040 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____2038 in
                FStar_List.append prefix1 uu____2036 in
              FStar_All.pipe_left FStar_Format.reduce uu____2034 in
        let docs1 =
          FStar_List.map
            (fun uu____2070  ->
               match uu____2070 with
               | (x,s,m) ->
                   let uu____2097 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2098 = for1_mod true (x, s, m) in
                   (uu____2097, uu____2098)) mllib in
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
        let uu____2118 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2118 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2128 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2128 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1