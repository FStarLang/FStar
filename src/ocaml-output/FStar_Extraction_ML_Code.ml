open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____62703 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____62714 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____62725 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____62736 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____62747 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____62763 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____62774 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____62786 -> false
  
let (__proj__Infix__item___0 : fixity -> assoc) =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int * fixity)
type level = (opprec * assoc)
let (t_prio_fun : (Prims.int * fixity)) =
  ((Prims.parse_int "10"), (Infix Right)) 
let (t_prio_tpl : (Prims.int * fixity)) =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let (t_prio_name : (Prims.int * fixity)) = ((Prims.parse_int "30"), Postfix) 
let (e_bin_prio_lambda : (Prims.int * fixity)) =
  ((Prims.parse_int "5"), Prefix) 
let (e_bin_prio_if : (Prims.int * fixity)) = ((Prims.parse_int "15"), Prefix) 
let (e_bin_prio_letin : (Prims.int * fixity)) =
  ((Prims.parse_int "19"), Prefix) 
let (e_bin_prio_or : (Prims.int * fixity)) =
  ((Prims.parse_int "20"), (Infix Left)) 
let (e_bin_prio_and : (Prims.int * fixity)) =
  ((Prims.parse_int "25"), (Infix Left)) 
let (e_bin_prio_eq : (Prims.int * fixity)) =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let (e_bin_prio_order : (Prims.int * fixity)) =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let (e_bin_prio_op1 : (Prims.int * fixity)) =
  ((Prims.parse_int "30"), (Infix Left)) 
let (e_bin_prio_op2 : (Prims.int * fixity)) =
  ((Prims.parse_int "40"), (Infix Left)) 
let (e_bin_prio_op3 : (Prims.int * fixity)) =
  ((Prims.parse_int "50"), (Infix Left)) 
let (e_bin_prio_op4 : (Prims.int * fixity)) =
  ((Prims.parse_int "60"), (Infix Left)) 
let (e_bin_prio_comb : (Prims.int * fixity)) =
  ((Prims.parse_int "70"), (Infix Left)) 
let (e_bin_prio_seq : (Prims.int * fixity)) =
  ((Prims.parse_int "100"), (Infix Left)) 
let (e_app_prio : (Prims.int * fixity)) =
  ((Prims.parse_int "10000"), (Infix Left)) 
let (min_op_prec : (Prims.int * fixity)) =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let (max_op_prec : (Prims.int * fixity)) =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns : 'a . ('a Prims.list * 'a Prims.list) -> Prims.bool =
  fun x  ->
    match x with
    | ([],uu____62984) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____63008,uu____63009) -> false
  
let (path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list)
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
                  let uu____63094 = FStar_Util.first_N cg_len ns  in
                  match uu____63094 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____63138 =
                           let uu____63142 =
                             let uu____63146 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____63146]  in
                           FStar_List.append pfx uu____63142  in
                         FStar_Pervasives_Native.Some uu____63138
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None)
            in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
  
let (mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath)
  =
  fun currentModule  ->
    fun x  ->
      let uu____63192 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____63192 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____63208 ->
          let uu____63210 = x  in
          (match uu____63210 with
           | (ns,x1) ->
               let uu____63221 = path_of_ns currentModule ns  in
               (uu____63221, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____63239 =
      let uu____63241 =
        let uu____63243 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____63243  in
      let uu____63246 = FStar_String.get s (Prims.parse_int "0")  in
      uu____63241 <> uu____63246  in
    if uu____63239 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____63282 = mlpath_of_mlpath currentModule mlp  in
         match uu____63282 with
         | (p,s) ->
             let uu____63294 =
               let uu____63298 =
                 let uu____63302 = ptsym_of_symbol s  in [uu____63302]  in
               FStar_List.append p uu____63298  in
             FStar_String.concat "." uu____63294)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____63323 = mlpath_of_mlpath currentModule mlp  in
      match uu____63323 with
      | (p,s) ->
          let s1 =
            let uu____63337 =
              let uu____63339 =
                let uu____63341 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____63341  in
              let uu____63344 = FStar_String.get s (Prims.parse_int "0")  in
              uu____63339 <> uu____63344  in
            if uu____63337 then Prims.op_Hat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
  
let (infix_prim_ops :
  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list) =
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
let (prim_uni_ops : unit -> (Prims.string * Prims.string) Prims.list) =
  fun uu____63707  ->
    let op_minus =
      let uu____63710 =
        let uu____63712 = FStar_Options.codegen ()  in
        uu____63712 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____63710 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____63761 . unit -> 'Auu____63761 Prims.list =
  fun uu____63764  -> [] 
let (prim_constructors : (Prims.string * Prims.string) Prims.list) =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let (is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool) =
  fun ns  -> ns = ["Prims"] 
let (as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) *
      Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu____63859  ->
    match uu____63859 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____63918  ->
               match uu____63918 with | (y,uu____63934,uu____63935) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____63973 = as_bin_op p  in
    uu____63973 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64030  ->
    match uu____64030 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____64058 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____64076  ->
               match uu____64076 with | (y,uu____64085) -> x = y) uu____64058
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64106 = as_uni_op p  in
    uu____64106 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64150  ->
    match uu____64150 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____64187  ->
               match uu____64187 with | (y,uu____64196) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64217 = as_standard_constructor p  in
    uu____64217 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____64267  ->
    fun inner  ->
      fun doc1  ->
        match uu____64267 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____64333 = _inner  in
              match uu____64333 with
              | (pi,fi) ->
                  let uu____64344 = _outer  in
                  (match uu____64344 with
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
                           | (uu____64362,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____64364,uu____64365) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
  
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x  -> Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x) 
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback  ->
    fun uu___543_64404  ->
      if uu___543_64404 = 92
      then "\\\\"
      else
        if uu___543_64404 = 32
        then " "
        else
          if uu___543_64404 = 8
          then "\\b"
          else
            if uu___543_64404 = 9
            then "\\t"
            else
              if uu___543_64404 = 13
              then "\\r"
              else
                if uu___543_64404 = 10
                then "\\n"
                else
                  if uu___543_64404 = 39
                  then "\\'"
                  else
                    if uu___543_64404 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_64404
                      then FStar_Util.string_of_char uu___543_64404
                      else
                        if FStar_Util.is_punctuation uu___543_64404
                        then FStar_Util.string_of_char uu___543_64404
                        else
                          if FStar_Util.is_symbol uu___543_64404
                          then FStar_Util.string_of_char uu___543_64404
                          else fallback uu___543_64404
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____64451 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____64451
          (if
             ((nc >= (Prims.parse_int "32")) &&
                (nc <= (Prims.parse_int "127")))
               && (nc <> (Prims.parse_int "34"))
           then
             Prims.op_Hat " (*"
               (Prims.op_Hat (FStar_Util.string_of_char c) "*)")
           else "")
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.op_Hat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.op_Hat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64515,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64529,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____64561 =
          let uu____64563 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____64563 "\""  in
        Prims.op_Hat "\"" uu____64561
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____64569 =
          let uu____64571 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____64571 "\""  in
        Prims.op_Hat "\"" uu____64569
    | uu____64575 ->
        failwith "TODO: extract integer constants properly into OCaml"
  
let rec (doc_of_mltype' :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s 95 117
              else s  in
            FStar_Format.text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc2 =
              let uu____64634 =
                let uu____64635 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____64635  in
              FStar_Format.parens uu____64634  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____64645 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____64651 =
                    let uu____64652 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____64652  in
                  FStar_Format.parens uu____64651
               in
            let name1 = ptsym currentModule name  in
            let uu____64656 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____64656
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____64658,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____64662 =
              let uu____64663 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____64663  in
            maybe_paren outer t_prio_fun uu____64662
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____64665 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64665
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased  -> FStar_Format.text "unit"

and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____64677 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____64677

let rec (doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____64770 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64770
            then
              let uu____64773 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____64773
            else
              (let uu____64777 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____64777)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs1 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs
               in
            let uu____64791 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____64791
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____64793 = string_of_mlconstant c  in
            FStar_Format.text uu____64793
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____64798 = ptsym currentModule path  in
            FStar_Format.text uu____64798
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____64832 =
              match uu____64832 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____64843 =
                    let uu____64846 =
                      let uu____64847 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____64847  in
                    [uu____64846; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____64843
               in
            let uu____64854 =
              let uu____64855 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____64855  in
            FStar_Format.cbrackets uu____64854
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____64869 = is_standard_constructor ctor  in
              if uu____64869
              then
                let uu____64873 =
                  let uu____64880 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64880  in
                FStar_Pervasives_Native.snd uu____64873
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____64907 = is_standard_constructor ctor  in
              if uu____64907
              then
                let uu____64911 =
                  let uu____64918 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64918  in
                FStar_Pervasives_Native.snd uu____64911
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
              | (uu____64951,uu____64952) ->
                  let uu____64959 =
                    let uu____64962 =
                      let uu____64965 =
                        let uu____64966 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____64966  in
                      [uu____64965]  in
                    (FStar_Format.text name) :: uu____64962  in
                  FStar_Format.reduce1 uu____64959
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____64977 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____64977) es
               in
            let docs1 =
              let uu____64979 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____64979  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____64996 =
                  let uu____64999 =
                    let uu____65002 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____65002]  in
                  FStar_Format.hardline :: uu____64999  in
                FStar_Format.reduce uu____64996
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____65011 =
              let uu____65012 =
                let uu____65015 =
                  let uu____65018 =
                    let uu____65021 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____65021]  in
                  doc1 :: uu____65018  in
                pre :: uu____65015  in
              FStar_Format.combine FStar_Format.hardline uu____65012  in
            FStar_Format.parens uu____65011
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____65032::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____65034;
                    FStar_Extraction_ML_Syntax.loc = uu____65035;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____65037)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____65039;
                  FStar_Extraction_ML_Syntax.loc = uu____65040;_}::[])
                 when
                 let uu____65084 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____65084 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____65110;
                            FStar_Extraction_ML_Syntax.loc = uu____65111;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____65113;
                       FStar_Extraction_ML_Syntax.loc = uu____65114;_} when
                       arg = arg' -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65172;
                   FStar_Extraction_ML_Syntax.loc = uu____65173;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65186;
                   FStar_Extraction_ML_Syntax.loc = uu____65187;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____65194 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____65205 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____65205)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____65210 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65210
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____65220 =
                   let uu____65223 =
                     let uu____65226 =
                       let uu____65229 =
                         let uu____65230 = ptsym currentModule f  in
                         FStar_Format.text uu____65230  in
                       [uu____65229]  in
                     (FStar_Format.text ".") :: uu____65226  in
                   e2 :: uu____65223  in
                 FStar_Format.reduce uu____65220)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____65266 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65266
              then
                let uu____65269 =
                  let uu____65272 =
                    let uu____65275 =
                      let uu____65278 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____65280 =
                              let uu____65283 =
                                let uu____65286 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____65286]  in
                              (FStar_Format.text " : ") :: uu____65283  in
                            FStar_Format.reduce1 uu____65280
                        | uu____65288 -> FStar_Format.text ""  in
                      [uu____65278; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____65275  in
                  (FStar_Format.text "(") :: uu____65272  in
                FStar_Format.reduce1 uu____65269
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____65307  ->
                   match uu____65307 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____65319 =
                let uu____65322 =
                  let uu____65325 = FStar_Format.reduce1 ids1  in
                  [uu____65325; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____65322  in
              FStar_Format.reduce1 uu____65319  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65334 =
                let uu____65337 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65341 =
                  let uu____65344 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____65344; FStar_Format.text "end"]  in
                uu____65337 :: uu____65341  in
              FStar_Format.combine FStar_Format.hardline uu____65334  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65353 =
                let uu____65356 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65360 =
                  let uu____65363 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____65364 =
                    let uu____65367 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____65371 =
                      let uu____65374 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____65374; FStar_Format.text "end"]  in
                    uu____65367 :: uu____65371  in
                  uu____65363 :: uu____65364  in
                uu____65356 :: uu____65360  in
              FStar_Format.combine FStar_Format.hardline uu____65353  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____65413 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____65413 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____65420 =
              let uu____65423 =
                let uu____65426 =
                  let uu____65427 = ptctor currentModule exn  in
                  FStar_Format.text uu____65427  in
                [uu____65426]  in
              (FStar_Format.text "raise") :: uu____65423  in
            FStar_Format.reduce1 uu____65420
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____65439 =
              let uu____65442 =
                let uu____65445 =
                  let uu____65446 = ptctor currentModule exn  in
                  FStar_Format.text uu____65446  in
                let uu____65448 =
                  let uu____65451 =
                    let uu____65452 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____65452  in
                  [uu____65451]  in
                uu____65445 :: uu____65448  in
              (FStar_Format.text "raise") :: uu____65442  in
            FStar_Format.reduce1 uu____65439
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____65477 =
              let uu____65480 =
                let uu____65483 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____65484 =
                  let uu____65487 =
                    let uu____65490 =
                      let uu____65491 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____65491
                       in
                    [uu____65490]  in
                  (FStar_Format.text "with") :: uu____65487  in
                uu____65483 :: uu____65484  in
              (FStar_Format.text "try") :: uu____65480  in
            FStar_Format.combine FStar_Format.hardline uu____65477
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1

and (doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____65515 =
            let uu____65529 = as_bin_op p  in FStar_Option.get uu____65529
             in
          match uu____65515 with
          | (uu____65558,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21]  in
              FStar_Format.parens doc1

and (doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____65582 =
          let uu____65589 = as_uni_op p  in FStar_Option.get uu____65589  in
        match uu____65582 with
        | (uu____65604,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11]
               in
            FStar_Format.parens doc1

and (doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____65617 = string_of_mlconstant c  in
          FStar_Format.text uu____65617
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____65653 =
            match uu____65653 with
            | (name,p) ->
                let uu____65663 =
                  let uu____65666 =
                    let uu____65667 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____65667  in
                  let uu____65673 =
                    let uu____65676 =
                      let uu____65679 = doc_of_pattern currentModule p  in
                      [uu____65679]  in
                    (FStar_Format.text "=") :: uu____65676  in
                  uu____65666 :: uu____65673  in
                FStar_Format.reduce1 uu____65663
             in
          let uu____65681 =
            let uu____65682 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____65682  in
          FStar_Format.cbrackets uu____65681
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____65696 = is_standard_constructor ctor  in
            if uu____65696
            then
              let uu____65700 =
                let uu____65707 = as_standard_constructor ctor  in
                FStar_Option.get uu____65707  in
              FStar_Pervasives_Native.snd uu____65700
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____65734 = is_standard_constructor ctor  in
            if uu____65734
            then
              let uu____65738 =
                let uu____65745 = as_standard_constructor ctor  in
                FStar_Option.get uu____65745  in
              FStar_Pervasives_Native.snd uu____65738
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____65774 =
                  let uu____65777 =
                    let uu____65778 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____65778  in
                  let uu____65779 =
                    let uu____65782 =
                      let uu____65785 = doc_of_pattern currentModule xs  in
                      [uu____65785]  in
                    (FStar_Format.text "::") :: uu____65782  in
                  uu____65777 :: uu____65779  in
                FStar_Format.reduce uu____65774
            | (uu____65787,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____65788)::[]) ->
                let uu____65795 =
                  let uu____65798 =
                    let uu____65801 =
                      let uu____65802 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____65802  in
                    [uu____65801]  in
                  (FStar_Format.text name) :: uu____65798  in
                FStar_Format.reduce1 uu____65795
            | uu____65803 ->
                let uu____65811 =
                  let uu____65814 =
                    let uu____65817 =
                      let uu____65818 =
                        let uu____65819 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____65819
                         in
                      FStar_Format.parens uu____65818  in
                    [uu____65817]  in
                  (FStar_Format.text name) :: uu____65814  in
                FStar_Format.reduce1 uu____65811
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____65834 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____65834
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65847  ->
      match uu____65847 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____65857 =
                  let uu____65860 =
                    let uu____65863 = doc_of_pattern currentModule p  in
                    [uu____65863]  in
                  (FStar_Format.text "|") :: uu____65860  in
                FStar_Format.reduce1 uu____65857
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____65867 =
                  let uu____65870 =
                    let uu____65873 = doc_of_pattern currentModule p  in
                    [uu____65873; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____65870  in
                FStar_Format.reduce1 uu____65867
             in
          let uu____65876 =
            let uu____65879 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____65882 =
              let uu____65885 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____65885; FStar_Format.text "end"]  in
            uu____65879 :: uu____65882  in
          FStar_Format.combine FStar_Format.hardline uu____65876

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65888  ->
      match uu____65888 with
      | (rec_,top_level,lets) ->
          let for1 uu____65913 =
            match uu____65913 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____65916;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____65918;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____65934 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____65934
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____65937::uu____65938,uu____65939) ->
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
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1]
                          | FStar_Pervasives_Native.Some (vs,ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty
                                 in
                              let vars =
                                let uu____65963 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____65963
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____65982 =
                  let uu____65985 =
                    let uu____65988 = FStar_Format.reduce1 ids  in
                    [uu____65988; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____65985  in
                FStar_Format.reduce1 uu____65982
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

and (doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc) =
  fun uu____66014  ->
    match uu____66014 with
    | (lineno,file) ->
        let uu____66021 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____66021
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))])

let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____66073 =
        match uu____66073 with
        | (uu____66096,x,mangle_opt,tparams,uu____66100,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____66135 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____66146 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____66146
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____66173 =
                    match uu____66173 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____66186 =
                    let uu____66187 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____66187
                     in
                  FStar_Format.cbrackets uu____66186
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____66228 =
                    match uu____66228 with
                    | (name,tys) ->
                        let uu____66259 = FStar_List.split tys  in
                        (match uu____66259 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____66282 ->
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
              let uu____66313 =
                let uu____66316 =
                  let uu____66319 =
                    let uu____66320 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____66320  in
                  [uu____66319]  in
                tparams1 :: uu____66316  in
              FStar_Format.reduce1 uu____66313  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____66329 =
                   let uu____66332 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____66332; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____66329)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____66340 =
            let uu____66343 =
              let uu____66346 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____66346]  in
            (FStar_Format.text "type") :: uu____66343  in
          FStar_Format.reduce1 uu____66340
        else FStar_Format.text ""  in
      doc2
  
let rec (doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____66382 =
            let uu____66385 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____66388 =
              let uu____66391 = doc_of_sig currentModule subsig  in
              let uu____66392 =
                let uu____66395 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____66395]  in
              uu____66391 :: uu____66392  in
            uu____66385 :: uu____66388  in
          FStar_Format.combine FStar_Format.hardline uu____66382
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____66415 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____66415  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____66420,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
             in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls

and (doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun s  ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s  in
      let docs1 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs
         in
      FStar_Format.reduce docs1

let (doc_of_mod1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc)
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
            let uu____66499 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____66499  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____66515 =
            let uu____66518 =
              let uu____66521 =
                let uu____66524 =
                  let uu____66527 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____66527]  in
                (FStar_Format.text "=") :: uu____66524  in
              (FStar_Format.text "_") :: uu____66521  in
            (FStar_Format.text "let") :: uu____66518  in
          FStar_Format.reduce1 uu____66515
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
  
let (doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x  in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____66557 ->
                  FStar_Format.empty
              | uu____66558 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____66571  ->
    match uu____66571 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____66641 =
          match uu____66641 with
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
                  (fun uu____66701  ->
                     match uu____66701 with
                     | (s,uu____66707) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____66728 =
                let uu____66731 =
                  let uu____66734 =
                    let uu____66737 = FStar_Format.reduce sub3  in
                    [uu____66737;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____66734
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____66731
                 in
              FStar_Format.reduce uu____66728
        
        and for1_mod istop uu____66740 =
          match uu____66740 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____66822 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____66843 =
                  let uu____66846 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____66846
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
                FStar_Format.reduce1 uu____66843  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66877  ->
                     match uu____66877 with
                     | (uu____66882,m) -> doc_of_mod target_mod_name m)
                  sigmod
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
                let uu____66908 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____66908
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____66916 =
                let uu____66919 =
                  let uu____66922 =
                    let uu____66925 =
                      let uu____66928 =
                        let uu____66931 =
                          let uu____66934 = FStar_Format.reduce sub3  in
                          [uu____66934;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____66931
                         in
                      FStar_Format.hardline :: uu____66928  in
                    FStar_List.append maybe_open_pervasives uu____66925  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____66922
                   in
                FStar_List.append prefix1 uu____66919  in
              FStar_All.pipe_left FStar_Format.reduce uu____66916
         in
        let docs =
          FStar_List.map
            (fun uu____66978  ->
               match uu____66978 with
               | (x,s,m) ->
                   let uu____67035 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____67037 = for1_mod true (x, s, m)  in
                   (uu____67035, uu____67037)) mllib
           in
        docs
  
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  = fun mllib  -> doc_of_mllib_r mllib 
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67080 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____67080 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67096 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____67096 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  