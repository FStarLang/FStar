open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____62731 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____62742 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____62753 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____62764 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____62775 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____62791 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____62802 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____62814 -> false
  
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
    | ([],uu____63012) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____63036,uu____63037) -> false
  
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
                  let uu____63122 = FStar_Util.first_N cg_len ns  in
                  match uu____63122 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____63166 =
                           let uu____63170 =
                             let uu____63174 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____63174]  in
                           FStar_List.append pfx uu____63170  in
                         FStar_Pervasives_Native.Some uu____63166
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
      let uu____63220 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____63220 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____63236 ->
          let uu____63238 = x  in
          (match uu____63238 with
           | (ns,x1) ->
               let uu____63249 = path_of_ns currentModule ns  in
               (uu____63249, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____63267 =
      let uu____63269 =
        let uu____63271 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____63271  in
      let uu____63274 = FStar_String.get s (Prims.parse_int "0")  in
      uu____63269 <> uu____63274  in
    if uu____63267 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____63310 = mlpath_of_mlpath currentModule mlp  in
         match uu____63310 with
         | (p,s) ->
             let uu____63322 =
               let uu____63326 =
                 let uu____63330 = ptsym_of_symbol s  in [uu____63330]  in
               FStar_List.append p uu____63326  in
             FStar_String.concat "." uu____63322)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____63351 = mlpath_of_mlpath currentModule mlp  in
      match uu____63351 with
      | (p,s) ->
          let s1 =
            let uu____63365 =
              let uu____63367 =
                let uu____63369 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____63369  in
              let uu____63372 = FStar_String.get s (Prims.parse_int "0")  in
              uu____63367 <> uu____63372  in
            if uu____63365 then Prims.op_Hat "U__" s else s  in
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
  fun uu____63735  ->
    let op_minus =
      let uu____63738 =
        let uu____63740 = FStar_Options.codegen ()  in
        uu____63740 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____63738 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____63789 . unit -> 'Auu____63789 Prims.list =
  fun uu____63792  -> [] 
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
  fun uu____63887  ->
    match uu____63887 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____63946  ->
               match uu____63946 with | (y,uu____63962,uu____63963) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64001 = as_bin_op p  in
    uu____64001 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64058  ->
    match uu____64058 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____64086 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____64104  ->
               match uu____64104 with | (y,uu____64113) -> x = y) uu____64086
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64134 = as_uni_op p  in
    uu____64134 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____64178  ->
    match uu____64178 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____64215  ->
               match uu____64215 with | (y,uu____64224) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____64245 = as_standard_constructor p  in
    uu____64245 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____64295  ->
    fun inner  ->
      fun doc1  ->
        match uu____64295 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____64361 = _inner  in
              match uu____64361 with
              | (pi,fi) ->
                  let uu____64372 = _outer  in
                  (match uu____64372 with
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
                           | (uu____64390,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____64392,uu____64393) -> false)))
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
    fun uu___543_64432  ->
      if uu___543_64432 = 92
      then "\\\\"
      else
        if uu___543_64432 = 32
        then " "
        else
          if uu___543_64432 = 8
          then "\\b"
          else
            if uu___543_64432 = 9
            then "\\t"
            else
              if uu___543_64432 = 13
              then "\\r"
              else
                if uu___543_64432 = 10
                then "\\n"
                else
                  if uu___543_64432 = 39
                  then "\\'"
                  else
                    if uu___543_64432 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_64432
                      then FStar_Util.string_of_char uu___543_64432
                      else
                        if FStar_Util.is_punctuation uu___543_64432
                        then FStar_Util.string_of_char uu___543_64432
                        else
                          if FStar_Util.is_symbol uu___543_64432
                          then FStar_Util.string_of_char uu___543_64432
                          else fallback uu___543_64432
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____64479 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____64479
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
        (s,FStar_Pervasives_Native.Some (uu____64543,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____64557,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____64589 =
          let uu____64591 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____64591 "\""  in
        Prims.op_Hat "\"" uu____64589
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____64597 =
          let uu____64599 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____64599 "\""  in
        Prims.op_Hat "\"" uu____64597
    | uu____64603 ->
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
              let uu____64662 =
                let uu____64663 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____64663  in
              FStar_Format.parens uu____64662  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____64673 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____64679 =
                    let uu____64680 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____64680  in
                  FStar_Format.parens uu____64679
               in
            let name1 = ptsym currentModule name  in
            let uu____64684 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____64684
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____64686,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____64690 =
              let uu____64691 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____64691  in
            maybe_paren outer t_prio_fun uu____64690
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____64693 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64693
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
        let uu____64705 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____64705

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
            let uu____64798 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____64798
            then
              let uu____64801 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____64801
            else
              (let uu____64805 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____64805)
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
            let uu____64819 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____64819
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____64821 = string_of_mlconstant c  in
            FStar_Format.text uu____64821
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____64826 = ptsym currentModule path  in
            FStar_Format.text uu____64826
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____64860 =
              match uu____64860 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____64871 =
                    let uu____64874 =
                      let uu____64875 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____64875  in
                    [uu____64874; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____64871
               in
            let uu____64882 =
              let uu____64883 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____64883  in
            FStar_Format.cbrackets uu____64882
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____64897 = is_standard_constructor ctor  in
              if uu____64897
              then
                let uu____64901 =
                  let uu____64908 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64908  in
                FStar_Pervasives_Native.snd uu____64901
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____64935 = is_standard_constructor ctor  in
              if uu____64935
              then
                let uu____64939 =
                  let uu____64946 = as_standard_constructor ctor  in
                  FStar_Option.get uu____64946  in
                FStar_Pervasives_Native.snd uu____64939
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
              | (uu____64979,uu____64980) ->
                  let uu____64987 =
                    let uu____64990 =
                      let uu____64993 =
                        let uu____64994 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____64994  in
                      [uu____64993]  in
                    (FStar_Format.text name) :: uu____64990  in
                  FStar_Format.reduce1 uu____64987
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____65005 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____65005) es
               in
            let docs1 =
              let uu____65007 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____65007  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____65024 =
                  let uu____65027 =
                    let uu____65030 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____65030]  in
                  FStar_Format.hardline :: uu____65027  in
                FStar_Format.reduce uu____65024
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____65039 =
              let uu____65040 =
                let uu____65043 =
                  let uu____65046 =
                    let uu____65049 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____65049]  in
                  doc1 :: uu____65046  in
                pre :: uu____65043  in
              FStar_Format.combine FStar_Format.hardline uu____65040  in
            FStar_Format.parens uu____65039
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____65060::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____65062;
                    FStar_Extraction_ML_Syntax.loc = uu____65063;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____65065)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____65067;
                  FStar_Extraction_ML_Syntax.loc = uu____65068;_}::[])
                 when
                 let uu____65112 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____65112 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____65138;
                            FStar_Extraction_ML_Syntax.loc = uu____65139;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____65141;
                       FStar_Extraction_ML_Syntax.loc = uu____65142;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65200;
                   FStar_Extraction_ML_Syntax.loc = uu____65201;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____65214;
                   FStar_Extraction_ML_Syntax.loc = uu____65215;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____65222 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____65233 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____65233)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____65238 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65238
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____65248 =
                   let uu____65251 =
                     let uu____65254 =
                       let uu____65257 =
                         let uu____65258 = ptsym currentModule f  in
                         FStar_Format.text uu____65258  in
                       [uu____65257]  in
                     (FStar_Format.text ".") :: uu____65254  in
                   e2 :: uu____65251  in
                 FStar_Format.reduce uu____65248)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____65294 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____65294
              then
                let uu____65297 =
                  let uu____65300 =
                    let uu____65303 =
                      let uu____65306 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____65308 =
                              let uu____65311 =
                                let uu____65314 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____65314]  in
                              (FStar_Format.text " : ") :: uu____65311  in
                            FStar_Format.reduce1 uu____65308
                        | uu____65316 -> FStar_Format.text ""  in
                      [uu____65306; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____65303  in
                  (FStar_Format.text "(") :: uu____65300  in
                FStar_Format.reduce1 uu____65297
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____65335  ->
                   match uu____65335 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____65347 =
                let uu____65350 =
                  let uu____65353 = FStar_Format.reduce1 ids1  in
                  [uu____65353; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____65350  in
              FStar_Format.reduce1 uu____65347  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65362 =
                let uu____65365 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65369 =
                  let uu____65372 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____65372; FStar_Format.text "end"]  in
                uu____65365 :: uu____65369  in
              FStar_Format.combine FStar_Format.hardline uu____65362  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____65381 =
                let uu____65384 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____65388 =
                  let uu____65391 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____65392 =
                    let uu____65395 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____65399 =
                      let uu____65402 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____65402; FStar_Format.text "end"]  in
                    uu____65395 :: uu____65399  in
                  uu____65391 :: uu____65392  in
                uu____65384 :: uu____65388  in
              FStar_Format.combine FStar_Format.hardline uu____65381  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____65441 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____65441 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____65448 =
              let uu____65451 =
                let uu____65454 =
                  let uu____65455 = ptctor currentModule exn  in
                  FStar_Format.text uu____65455  in
                [uu____65454]  in
              (FStar_Format.text "raise") :: uu____65451  in
            FStar_Format.reduce1 uu____65448
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____65467 =
              let uu____65470 =
                let uu____65473 =
                  let uu____65474 = ptctor currentModule exn  in
                  FStar_Format.text uu____65474  in
                let uu____65476 =
                  let uu____65479 =
                    let uu____65480 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____65480  in
                  [uu____65479]  in
                uu____65473 :: uu____65476  in
              (FStar_Format.text "raise") :: uu____65470  in
            FStar_Format.reduce1 uu____65467
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____65505 =
              let uu____65508 =
                let uu____65511 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____65512 =
                  let uu____65515 =
                    let uu____65518 =
                      let uu____65519 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____65519
                       in
                    [uu____65518]  in
                  (FStar_Format.text "with") :: uu____65515  in
                uu____65511 :: uu____65512  in
              (FStar_Format.text "try") :: uu____65508  in
            FStar_Format.combine FStar_Format.hardline uu____65505
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
          let uu____65543 =
            let uu____65557 = as_bin_op p  in FStar_Option.get uu____65557
             in
          match uu____65543 with
          | (uu____65586,prio,txt) ->
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
        let uu____65610 =
          let uu____65617 = as_uni_op p  in FStar_Option.get uu____65617  in
        match uu____65610 with
        | (uu____65632,txt) ->
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
          let uu____65645 = string_of_mlconstant c  in
          FStar_Format.text uu____65645
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____65681 =
            match uu____65681 with
            | (name,p) ->
                let uu____65691 =
                  let uu____65694 =
                    let uu____65695 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____65695  in
                  let uu____65701 =
                    let uu____65704 =
                      let uu____65707 = doc_of_pattern currentModule p  in
                      [uu____65707]  in
                    (FStar_Format.text "=") :: uu____65704  in
                  uu____65694 :: uu____65701  in
                FStar_Format.reduce1 uu____65691
             in
          let uu____65709 =
            let uu____65710 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____65710  in
          FStar_Format.cbrackets uu____65709
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____65724 = is_standard_constructor ctor  in
            if uu____65724
            then
              let uu____65728 =
                let uu____65735 = as_standard_constructor ctor  in
                FStar_Option.get uu____65735  in
              FStar_Pervasives_Native.snd uu____65728
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____65762 = is_standard_constructor ctor  in
            if uu____65762
            then
              let uu____65766 =
                let uu____65773 = as_standard_constructor ctor  in
                FStar_Option.get uu____65773  in
              FStar_Pervasives_Native.snd uu____65766
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____65802 =
                  let uu____65805 =
                    let uu____65806 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____65806  in
                  let uu____65807 =
                    let uu____65810 =
                      let uu____65813 = doc_of_pattern currentModule xs  in
                      [uu____65813]  in
                    (FStar_Format.text "::") :: uu____65810  in
                  uu____65805 :: uu____65807  in
                FStar_Format.reduce uu____65802
            | (uu____65815,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____65816)::[]) ->
                let uu____65823 =
                  let uu____65826 =
                    let uu____65829 =
                      let uu____65830 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____65830  in
                    [uu____65829]  in
                  (FStar_Format.text name) :: uu____65826  in
                FStar_Format.reduce1 uu____65823
            | uu____65831 ->
                let uu____65839 =
                  let uu____65842 =
                    let uu____65845 =
                      let uu____65846 =
                        let uu____65847 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____65847
                         in
                      FStar_Format.parens uu____65846  in
                    [uu____65845]  in
                  (FStar_Format.text name) :: uu____65842  in
                FStar_Format.reduce1 uu____65839
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____65862 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____65862
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65875  ->
      match uu____65875 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____65885 =
                  let uu____65888 =
                    let uu____65891 = doc_of_pattern currentModule p  in
                    [uu____65891]  in
                  (FStar_Format.text "|") :: uu____65888  in
                FStar_Format.reduce1 uu____65885
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____65895 =
                  let uu____65898 =
                    let uu____65901 = doc_of_pattern currentModule p  in
                    [uu____65901; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____65898  in
                FStar_Format.reduce1 uu____65895
             in
          let uu____65904 =
            let uu____65907 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____65910 =
              let uu____65913 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____65913; FStar_Format.text "end"]  in
            uu____65907 :: uu____65910  in
          FStar_Format.combine FStar_Format.hardline uu____65904

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____65916  ->
      match uu____65916 with
      | (rec_,top_level,lets) ->
          let for1 uu____65941 =
            match uu____65941 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____65944;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____65946;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____65962 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____65962
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____65965::uu____65966,uu____65967) ->
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
                                let uu____65991 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____65991
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____66010 =
                  let uu____66013 =
                    let uu____66016 = FStar_Format.reduce1 ids  in
                    [uu____66016; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____66013  in
                FStar_Format.reduce1 uu____66010
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
  fun uu____66042  ->
    match uu____66042 with
    | (lineno,file) ->
        let uu____66049 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____66049
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
      let for1 uu____66101 =
        match uu____66101 with
        | (uu____66124,x,mangle_opt,tparams,uu____66128,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____66163 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____66174 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____66174
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____66201 =
                    match uu____66201 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____66214 =
                    let uu____66215 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____66215
                     in
                  FStar_Format.cbrackets uu____66214
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____66256 =
                    match uu____66256 with
                    | (name,tys) ->
                        let uu____66287 = FStar_List.split tys  in
                        (match uu____66287 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____66310 ->
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
              let uu____66341 =
                let uu____66344 =
                  let uu____66347 =
                    let uu____66348 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____66348  in
                  [uu____66347]  in
                tparams1 :: uu____66344  in
              FStar_Format.reduce1 uu____66341  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____66357 =
                   let uu____66360 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____66360; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____66357)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____66368 =
            let uu____66371 =
              let uu____66374 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____66374]  in
            (FStar_Format.text "type") :: uu____66371  in
          FStar_Format.reduce1 uu____66368
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
          let uu____66410 =
            let uu____66413 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____66416 =
              let uu____66419 = doc_of_sig currentModule subsig  in
              let uu____66420 =
                let uu____66423 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____66423]  in
              uu____66419 :: uu____66420  in
            uu____66413 :: uu____66416  in
          FStar_Format.combine FStar_Format.hardline uu____66410
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____66443 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____66443  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____66448,ty)) ->
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
            let uu____66527 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____66527  in
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
          let uu____66543 =
            let uu____66546 =
              let uu____66549 =
                let uu____66552 =
                  let uu____66555 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____66555]  in
                (FStar_Format.text "=") :: uu____66552  in
              (FStar_Format.text "_") :: uu____66549  in
            (FStar_Format.text "let") :: uu____66546  in
          FStar_Format.reduce1 uu____66543
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____66585 ->
                  FStar_Format.empty
              | uu____66586 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____66599  ->
    match uu____66599 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____66669 =
          match uu____66669 with
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
                  (fun uu____66729  ->
                     match uu____66729 with
                     | (s,uu____66735) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____66756 =
                let uu____66759 =
                  let uu____66762 =
                    let uu____66765 = FStar_Format.reduce sub3  in
                    [uu____66765;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____66762
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____66759
                 in
              FStar_Format.reduce uu____66756
        
        and for1_mod istop uu____66768 =
          match uu____66768 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____66850 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____66871 =
                  let uu____66874 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____66874
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
                FStar_Format.reduce1 uu____66871  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____66905  ->
                     match uu____66905 with
                     | (uu____66910,m) -> doc_of_mod target_mod_name m)
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
                let uu____66936 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____66936
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____66944 =
                let uu____66947 =
                  let uu____66950 =
                    let uu____66953 =
                      let uu____66956 =
                        let uu____66959 =
                          let uu____66962 = FStar_Format.reduce sub3  in
                          [uu____66962;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____66959
                         in
                      FStar_Format.hardline :: uu____66956  in
                    FStar_List.append maybe_open_pervasives uu____66953  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____66950
                   in
                FStar_List.append prefix1 uu____66947  in
              FStar_All.pipe_left FStar_Format.reduce uu____66944
         in
        let docs =
          FStar_List.map
            (fun uu____67006  ->
               match uu____67006 with
               | (x,s,m) ->
                   let uu____67063 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____67065 = for1_mod true (x, s, m)  in
                   (uu____67063, uu____67065)) mllib
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
        let uu____67108 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____67108 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____67124 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____67124 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  