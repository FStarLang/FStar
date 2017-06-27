open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let uu___is_ILeft : assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____4 -> false 
let uu___is_IRight : assoc -> Prims.bool =
  fun projectee  -> match projectee with | IRight  -> true | uu____8 -> false 
let uu___is_Left : assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____12 -> false 
let uu___is_Right : assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____16 -> false 
let uu___is_NonAssoc : assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____20 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let uu___is_Prefix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____28 -> false
  
let uu___is_Postfix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____32 -> false
  
let uu___is_Infix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____37 -> false
  
let __proj__Infix__item___0 : fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
let t_prio_fun : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10"), (Infix Right)) 
let t_prio_tpl : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let t_prio_name : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), Postfix) 
let e_bin_prio_lambda : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "5"), Prefix) 
let e_bin_prio_if : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "15"), Prefix) 
let e_bin_prio_letin : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "19"), Prefix) 
let e_bin_prio_or : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix Left)) 
let e_bin_prio_and : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "25"), (Infix Left)) 
let e_bin_prio_eq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let e_bin_prio_order : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let e_bin_prio_op1 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), (Infix Left)) 
let e_bin_prio_op2 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "40"), (Infix Left)) 
let e_bin_prio_op3 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "50"), (Infix Left)) 
let e_bin_prio_op4 : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "60"), (Infix Left)) 
let e_bin_prio_comb : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "70"), (Infix Left)) 
let e_bin_prio_seq : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "100"), (Infix Left)) 
let e_app_prio : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10000"), (Infix Left)) 
let min_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let max_op_prec : (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns x =
  match x with
  | ([],uu____102) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____116,uu____117) -> false 
let path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
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
                  let uu____155 = FStar_Util.first_N cg_len ns  in
                  match uu____155 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____173 =
                           let uu____175 =
                             let uu____177 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____177]  in
                           FStar_List.append pfx uu____175  in
                         FStar_Pervasives_Native.Some uu____173
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None)
            in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
  
let mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____194 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____194 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____197 ->
          let uu____198 = x  in
          (match uu____198 with
           | (ns,x1) ->
               let uu____203 = path_of_ns currentModule ns  in
               (uu____203, x1))
  
let ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____209 =
      let uu____210 =
        let uu____211 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____211  in
      let uu____212 = FStar_String.get s (Prims.parse_int "0")  in
      uu____210 <> uu____212  in
    if uu____209 then Prims.strcat "l__" s else s
  
let ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____223 = mlpath_of_mlpath currentModule mlp  in
         match uu____223 with
         | (p,s) ->
             let uu____228 =
               let uu____230 =
                 let uu____232 = ptsym_of_symbol s  in [uu____232]  in
               FStar_List.append p uu____230  in
             FStar_String.concat "." uu____228)
  
let ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____239 = mlpath_of_mlpath currentModule mlp  in
      match uu____239 with
      | (p,s) ->
          let s1 =
            let uu____245 =
              let uu____246 =
                let uu____247 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____247  in
              let uu____248 = FStar_String.get s (Prims.parse_int "0")  in
              uu____246 <> uu____248  in
            if uu____245 then Prims.strcat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
  
let infix_prim_ops :
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
let prim_uni_ops :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")] 
let prim_types uu____373 = [] 
let prim_constructors :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool =
  fun ns  -> ns = ["Prims"] 
let as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option
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
        else FStar_Pervasives_Native.None
  
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____445 = as_bin_op p  in uu____445 <> FStar_Pervasives_Native.None
  
let as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____468  ->
    match uu____468 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____481  -> match uu____481 with | (y,uu____485) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
  
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____492 = as_uni_op p  in uu____492 <> FStar_Pervasives_Native.None
  
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false 
let as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____509  ->
    match uu____509 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____522  -> match uu____522 with | (y,uu____526) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____533 = as_standard_constructor p  in
    uu____533 <> FStar_Pervasives_Native.None
  
let maybe_paren :
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____554  ->
    fun inner  ->
      fun doc1  ->
        match uu____554 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____587 = _inner  in
              match uu____587 with
              | (pi,fi) ->
                  let uu____592 = _outer  in
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
                           | (uu____598,uu____599) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let escape_byte_hex : FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let escape_char_hex : FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let escape_or :
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
  
let string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let uu____634 =
          let uu____635 = escape_or escape_char_hex c  in
          Prims.strcat uu____635 "'"  in
        Prims.strcat "'" uu____634
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____649,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____656,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____671 =
          let uu____672 = FStar_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat uu____672 "\""  in
        Prims.strcat "\"" uu____671
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____674 =
          let uu____675 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat uu____675 "\""  in
        Prims.strcat "\"" uu____674
    | uu____676 ->
        failwith "TODO: extract integer constants properly into OCaml"
  
let rec doc_of_mltype' :
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
              else s  in
            let uu____698 =
              let uu____699 = FStar_Extraction_ML_Syntax.idsym x  in
              FStar_All.pipe_left escape_tyvar uu____699  in
            FStar_Format.text uu____698
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc2 =
              let uu____707 =
                let uu____708 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____708  in
              FStar_Format.parens uu____707  in
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
                      args
                     in
                  let uu____723 =
                    let uu____724 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____724  in
                  FStar_Format.parens uu____723
               in
            let name1 = ptsym currentModule name  in
            let uu____726 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____726
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____728,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____736 =
              let uu____737 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____737  in
            maybe_paren outer t_prio_fun uu____736
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____738 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____738
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"

and doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____743 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____743

let rec doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____791 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____791
            then
              let uu____792 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1]
                 in
              FStar_Format.parens uu____792
            else
              (let uu____794 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____794)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1
               in
            let uu____804 = FStar_Format.reduce docs2  in
            FStar_Format.parens uu____804
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____806 = string_of_mlconstant c  in
            FStar_Format.text uu____806
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____808) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____810 = ptsym currentModule path  in
            FStar_Format.text uu____810
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____826 =
              match uu____826 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____834 =
                    let uu____836 =
                      let uu____837 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____837  in
                    [uu____836; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____834
               in
            let uu____839 =
              let uu____840 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____840  in
            FStar_Format.cbrackets uu____839
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____847 = is_standard_constructor ctor  in
              if uu____847
              then
                let uu____848 =
                  let uu____851 = as_standard_constructor ctor  in
                  FStar_Option.get uu____851  in
                FStar_Pervasives_Native.snd uu____848
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____863 = is_standard_constructor ctor  in
              if uu____863
              then
                let uu____864 =
                  let uu____867 = as_standard_constructor ctor  in
                  FStar_Option.get uu____867  in
                FStar_Pervasives_Native.snd uu____864
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
              | (uu____883,uu____884) ->
                  let uu____887 =
                    let uu____889 =
                      let uu____891 =
                        let uu____892 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____892  in
                      [uu____891]  in
                    (FStar_Format.text name) :: uu____889  in
                  FStar_Format.reduce1 uu____887
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____898 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____898) es
               in
            let docs2 =
              let uu____902 =
                FStar_Format.combine (FStar_Format.text ", ") docs1  in
              FStar_Format.parens uu____902  in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____904,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____914 =
                  let uu____916 =
                    let uu____918 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____918]  in
                  FStar_Format.hardline :: uu____916  in
                FStar_Format.reduce uu____914
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____925 =
              let uu____926 =
                let uu____928 =
                  let uu____930 =
                    let uu____932 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____932]  in
                  doc1 :: uu____930  in
                pre :: uu____928  in
              FStar_Format.combine FStar_Format.hardline uu____926  in
            FStar_Format.parens uu____925
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____939::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____941;
                    FStar_Extraction_ML_Syntax.loc = uu____942;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____944)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____946;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____947;_}::[])
                 when
                 let uu____965 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____965 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____978;
                            FStar_Extraction_ML_Syntax.loc = uu____979;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____981;
                       FStar_Extraction_ML_Syntax.loc = uu____982;_} when
                       let uu____993 = FStar_Extraction_ML_Syntax.idsym arg
                          in
                       let uu____994 = FStar_Extraction_ML_Syntax.idsym arg'
                          in
                       uu____993 = uu____994 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1015;
                   FStar_Extraction_ML_Syntax.loc = uu____1016;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1026;
                   FStar_Extraction_ML_Syntax.loc = uu____1027;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1032 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____1043 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____1043)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____1050 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1050
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1053 =
                   let uu____1055 =
                     let uu____1057 =
                       let uu____1059 =
                         let uu____1060 = ptsym currentModule f  in
                         FStar_Format.text uu____1060  in
                       [uu____1059]  in
                     (FStar_Format.text ".") :: uu____1057  in
                   e2 :: uu____1055  in
                 FStar_Format.reduce uu____1053)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1078 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1078
              then
                let uu____1079 =
                  let uu____1081 =
                    let uu____1083 =
                      let uu____1085 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1087 =
                              let uu____1089 =
                                let uu____1091 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____1091]  in
                              (FStar_Format.text " : ") :: uu____1089  in
                            FStar_Format.reduce1 uu____1087
                        | uu____1092 -> FStar_Format.text ""  in
                      [uu____1085; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____1083  in
                  (FStar_Format.text "(") :: uu____1081  in
                FStar_Format.reduce1 uu____1079
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____1101  ->
                   match uu____1101 with
                   | ((x,uu____1107),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____1115 =
                let uu____1117 =
                  let uu____1119 = FStar_Format.reduce1 ids1  in
                  [uu____1119; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____1117  in
              FStar_Format.reduce1 uu____1115  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1127 =
                let uu____1129 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1130 =
                  let uu____1132 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____1132; FStar_Format.text "end"]  in
                uu____1129 :: uu____1130  in
              FStar_Format.combine FStar_Format.hardline uu____1127  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1143 =
                let uu____1145 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1146 =
                  let uu____1148 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1151 =
                    let uu____1153 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____1154 =
                      let uu____1156 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____1156; FStar_Format.text "end"]  in
                    uu____1153 :: uu____1154  in
                  uu____1148 :: uu____1151  in
                uu____1145 :: uu____1146  in
              FStar_Format.combine FStar_Format.hardline uu____1143  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____1178 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____1178 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1182 =
              let uu____1184 =
                let uu____1186 =
                  let uu____1187 = ptctor currentModule exn  in
                  FStar_Format.text uu____1187  in
                [uu____1186]  in
              (FStar_Format.text "raise") :: uu____1184  in
            FStar_Format.reduce1 uu____1182
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____1196 =
              let uu____1198 =
                let uu____1200 =
                  let uu____1201 = ptctor currentModule exn  in
                  FStar_Format.text uu____1201  in
                let uu____1202 =
                  let uu____1204 =
                    let uu____1205 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____1205  in
                  [uu____1204]  in
                uu____1200 :: uu____1202  in
              (FStar_Format.text "raise") :: uu____1198  in
            FStar_Format.reduce1 uu____1196
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1218 =
              let uu____1220 =
                let uu____1222 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____1225 =
                  let uu____1227 =
                    let uu____1229 =
                      let uu____1230 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____1230
                       in
                    [uu____1229]  in
                  (FStar_Format.text "with") :: uu____1227  in
                uu____1222 :: uu____1225  in
              (FStar_Format.text "try") :: uu____1220  in
            FStar_Format.combine FStar_Format.hardline uu____1218

and doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____1236 =
            let uu____1242 = as_bin_op p  in FStar_Option.get uu____1242  in
          match uu____1236 with
          | (uu____1254,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21]  in
              FStar_Format.parens doc1

and doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____1271 =
          let uu____1274 = as_uni_op p  in FStar_Option.get uu____1274  in
        match uu____1271 with
        | (uu____1280,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11]
               in
            FStar_Format.parens doc1

and doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____1289 = string_of_mlconstant c  in
          FStar_Format.text uu____1289
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1306 =
            match uu____1306 with
            | (name,p) ->
                let uu____1311 =
                  let uu____1313 =
                    let uu____1314 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____1314  in
                  let uu____1316 =
                    let uu____1318 =
                      let uu____1320 = doc_of_pattern currentModule p  in
                      [uu____1320]  in
                    (FStar_Format.text "=") :: uu____1318  in
                  uu____1313 :: uu____1316  in
                FStar_Format.reduce1 uu____1311
             in
          let uu____1321 =
            let uu____1322 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____1322  in
          FStar_Format.cbrackets uu____1321
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1329 = is_standard_constructor ctor  in
            if uu____1329
            then
              let uu____1330 =
                let uu____1333 = as_standard_constructor ctor  in
                FStar_Option.get uu____1333  in
              FStar_Pervasives_Native.snd uu____1330
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1345 = is_standard_constructor ctor  in
            if uu____1345
            then
              let uu____1346 =
                let uu____1349 = as_standard_constructor ctor  in
                FStar_Option.get uu____1349  in
              FStar_Pervasives_Native.snd uu____1346
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1361 =
                  let uu____1363 =
                    let uu____1364 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____1364  in
                  let uu____1365 =
                    let uu____1367 =
                      let uu____1369 = doc_of_pattern currentModule xs  in
                      [uu____1369]  in
                    (FStar_Format.text "::") :: uu____1367  in
                  uu____1363 :: uu____1365  in
                FStar_Format.reduce uu____1361
            | (uu____1370,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1371)::[]) ->
                let uu____1374 =
                  let uu____1376 =
                    let uu____1378 =
                      let uu____1379 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____1379  in
                    [uu____1378]  in
                  (FStar_Format.text name) :: uu____1376  in
                FStar_Format.reduce1 uu____1374
            | uu____1380 ->
                let uu____1384 =
                  let uu____1386 =
                    let uu____1388 =
                      let uu____1389 =
                        let uu____1390 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1390
                         in
                      FStar_Format.parens uu____1389  in
                    [uu____1388]  in
                  (FStar_Format.text name) :: uu____1386  in
                FStar_Format.reduce1 uu____1384
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____1398 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____1398
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1406  ->
      match uu____1406 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____1413 =
                  let uu____1415 =
                    let uu____1417 = doc_of_pattern currentModule p  in
                    [uu____1417]  in
                  (FStar_Format.text "|") :: uu____1415  in
                FStar_Format.reduce1 uu____1413
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____1422 =
                  let uu____1424 =
                    let uu____1426 = doc_of_pattern currentModule p  in
                    [uu____1426; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____1424  in
                FStar_Format.reduce1 uu____1422
             in
          let uu____1427 =
            let uu____1429 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____1430 =
              let uu____1432 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____1432; FStar_Format.text "end"]  in
            uu____1429 :: uu____1430  in
          FStar_Format.combine FStar_Format.hardline uu____1427

and doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1436  ->
      match uu____1436 with
      | (rec_,top_level,lets) ->
          let for1 uu____1449 =
            match uu____1449 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1452;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1463 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____1463
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____1464::uu____1465,uu____1466) ->
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
                          | FStar_Pervasives_Native.Some
                              (uu____1481::uu____1482,uu____1483) ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "")
                   in
                let uu____1498 =
                  let uu____1500 =
                    let uu____1501 = FStar_Extraction_ML_Syntax.idsym name
                       in
                    FStar_Format.text uu____1501  in
                  let uu____1502 =
                    let uu____1504 = FStar_Format.reduce1 ids  in
                    [uu____1504; ty_annot; FStar_Format.text "="; e1]  in
                  uu____1500 :: uu____1502  in
                FStar_Format.reduce1 uu____1498
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

and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____1514  ->
    match uu____1514 with
    | (lineno,file) ->
        let uu____1517 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ())
           in
        if uu____1517
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])

let doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____1537 =
        match uu____1537 with
        | (uu____1546,x,mangle_opt,tparams,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1561 = FStar_Extraction_ML_Syntax.idsym x2  in
                  FStar_Format.text uu____1561
              | uu____1562 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1567 = FStar_Extraction_ML_Syntax.idsym x2
                            in
                         FStar_Format.text uu____1567) tparams
                     in
                  let uu____1568 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____1568
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1585 =
                    match uu____1585 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____1594 =
                    let uu____1595 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1595
                     in
                  FStar_Format.cbrackets uu____1594
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1614 =
                    match uu____1614 with
                    | (name,tys) ->
                        let uu____1628 = FStar_List.split tys  in
                        (match uu____1628 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1639 ->
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
              let uu____1657 =
                let uu____1659 =
                  let uu____1661 =
                    let uu____1662 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____1662  in
                  [uu____1661]  in
                tparams1 :: uu____1659  in
              FStar_Format.reduce1 uu____1657  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____1666 =
                   let uu____1668 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____1668; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____1666)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1683 =
            let uu____1685 =
              let uu____1687 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____1687]  in
            (FStar_Format.text "type") :: uu____1685  in
          FStar_Format.reduce1 uu____1683
        else FStar_Format.text ""  in
      doc2
  
let rec doc_of_sig1 :
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
                FStar_Format.text "="]
               in
            let uu____1706 =
              let uu____1708 = doc_of_sig currentModule subsig  in
              let uu____1709 =
                let uu____1711 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____1711]  in
              uu____1708 :: uu____1709  in
            uu____1705 :: uu____1706  in
          FStar_Format.combine FStar_Format.hardline uu____1703
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____1723 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____1723  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1725,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
             in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls

and doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      let docs1 = FStar_List.map (doc_of_sig1 currentModule) s  in
      let docs2 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs1
         in
      FStar_Format.reduce docs2

let doc_of_mod1 :
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
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args  in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1
             in
          let args3 =
            let uu____1769 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____1769  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1772,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1778 =
            let uu____1780 =
              let uu____1782 =
                let uu____1784 =
                  let uu____1786 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____1786]  in
                (FStar_Format.text "=") :: uu____1784  in
              (FStar_Format.text "_") :: uu____1782  in
            (FStar_Format.text "let") :: uu____1780  in
          FStar_Format.reduce1 uu____1778
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
  
let doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs1 =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x  in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1802 ->
                  FStar_Format.empty
              | uu____1803 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs1)
  
let rec doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1809  ->
    match uu____1809 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1847 =
          match uu____1847 with
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
                  (fun uu____1886  ->
                     match uu____1886 with
                     | (s,uu____1890) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____1905 =
                let uu____1907 =
                  let uu____1909 =
                    let uu____1911 = FStar_Format.reduce sub3  in
                    [uu____1911;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____1909
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1907
                 in
              FStar_Format.reduce uu____1905
        
        and for1_mod istop uu____1914 =
          match uu____1914 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name  in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____1951 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)]
                 in
              let head1 =
                let uu____1958 =
                  let uu____1960 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____1960
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
                FStar_Format.reduce1 uu____1958  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____1971  ->
                     match uu____1971 with
                     | (uu____1974,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____1992 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____1992
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____1995 =
                let uu____1997 =
                  let uu____1999 =
                    let uu____2001 =
                      let uu____2003 =
                        let uu____2005 =
                          let uu____2007 = FStar_Format.reduce sub3  in
                          [uu____2007;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2005
                         in
                      FStar_Format.hardline :: uu____2003  in
                    FStar_List.append maybe_open_pervasives uu____2001  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____1999
                   in
                FStar_List.append prefix1 uu____1997  in
              FStar_All.pipe_left FStar_Format.reduce uu____1995
         in
        let docs1 =
          FStar_List.map
            (fun uu____2025  ->
               match uu____2025 with
               | (x,s,m) ->
                   let uu____2052 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____2053 = for1_mod true (x, s, m)  in
                   (uu____2052, uu____2053)) mllib
           in
        docs1
  
let doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib 
let string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2073 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____2073 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2083 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____2083 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  