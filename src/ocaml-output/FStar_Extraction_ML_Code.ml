open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | ILeft  -> true | uu____57985 -> false
  
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____57996 -> false
  
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____58007 -> false
  
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____58018 -> false
  
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____58029 -> false
  
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____58045 -> false
  
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____58056 -> false
  
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____58068 -> false
  
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
    | ([],uu____58265) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____58289,uu____58290) -> false
  
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
                  let uu____58371 = FStar_Util.first_N cg_len ns  in
                  match uu____58371 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____58411 =
                           let uu____58415 =
                             let uu____58419 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____58419]  in
                           FStar_List.append pfx uu____58415  in
                         FStar_Pervasives_Native.Some uu____58411
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
      let uu____58465 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____58465 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____58481 ->
          let uu____58483 = x  in
          (match uu____58483 with
           | (ns,x1) ->
               let uu____58494 = path_of_ns currentModule ns  in
               (uu____58494, x1))
  
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s  ->
    let uu____58512 =
      let uu____58514 =
        let uu____58516 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____58516  in
      let uu____58519 = FStar_String.get s (Prims.parse_int "0")  in
      uu____58514 <> uu____58519  in
    if uu____58512 then Prims.op_Hat "l__" s else s
  
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____58555 = mlpath_of_mlpath currentModule mlp  in
         match uu____58555 with
         | (p,s) ->
             let uu____58567 =
               let uu____58571 =
                 let uu____58575 = ptsym_of_symbol s  in [uu____58575]  in
               FStar_List.append p uu____58571  in
             FStar_String.concat "." uu____58567)
  
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____58596 = mlpath_of_mlpath currentModule mlp  in
      match uu____58596 with
      | (p,s) ->
          let s1 =
            let uu____58610 =
              let uu____58612 =
                let uu____58614 = FStar_String.get s (Prims.parse_int "0")
                   in
                FStar_Char.uppercase uu____58614  in
              let uu____58617 = FStar_String.get s (Prims.parse_int "0")  in
              uu____58612 <> uu____58617  in
            if uu____58610 then Prims.op_Hat "U__" s else s  in
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
  fun uu____58980  ->
    let op_minus =
      let uu____58983 =
        let uu____58985 = FStar_Options.codegen ()  in
        uu____58985 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____58983 then "-" else "~-"  in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
  
let prim_types : 'Auu____59034 . unit -> 'Auu____59034 Prims.list =
  fun uu____59037  -> [] 
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
  fun uu____59132  ->
    match uu____59132 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59191  ->
               match uu____59191 with | (y,uu____59207,uu____59208) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
  
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59246 = as_bin_op p  in
    uu____59246 <> FStar_Pervasives_Native.None
  
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59303  ->
    match uu____59303 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____59331 = prim_uni_ops ()  in
          FStar_List.tryFind
            (fun uu____59349  ->
               match uu____59349 with | (y,uu____59358) -> x = y) uu____59331
        else FStar_Pervasives_Native.None
  
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59379 = as_uni_op p  in
    uu____59379 <> FStar_Pervasives_Native.None
  
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  -> false 
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu____59423  ->
    match uu____59423 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____59460  ->
               match uu____59460 with | (y,uu____59469) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
  
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p  ->
    let uu____59490 = as_standard_constructor p  in
    uu____59490 <> FStar_Pervasives_Native.None
  
let (maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc)
  =
  fun uu____59540  ->
    fun inner  ->
      fun doc1  ->
        match uu____59540 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____59606 = _inner  in
              match uu____59606 with
              | (pi,fi) ->
                  let uu____59617 = _outer  in
                  (match uu____59617 with
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
                           | (uu____59635,NonAssoc ) ->
                               (pi = po) && (fi = fo)
                           | (uu____59637,uu____59638) -> false)))
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
    fun uu___543_59677  ->
      if uu___543_59677 = 92
      then "\\\\"
      else
        if uu___543_59677 = 32
        then " "
        else
          if uu___543_59677 = 8
          then "\\b"
          else
            if uu___543_59677 = 9
            then "\\t"
            else
              if uu___543_59677 = 13
              then "\\r"
              else
                if uu___543_59677 = 10
                then "\\n"
                else
                  if uu___543_59677 = 39
                  then "\\'"
                  else
                    if uu___543_59677 = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___543_59677
                      then FStar_Util.string_of_char uu___543_59677
                      else
                        if FStar_Util.is_punctuation uu___543_59677
                        then FStar_Util.string_of_char uu___543_59677
                        else
                          if FStar_Util.is_symbol uu___543_59677
                          then FStar_Util.string_of_char uu___543_59677
                          else fallback uu___543_59677
  
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c  in
        let uu____59724 = FStar_Util.string_of_int nc  in
        Prims.op_Hat uu____59724
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
        (s,FStar_Pervasives_Native.Some (uu____59766,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____59780,FStar_Const.Int16 )) ->
        s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____59812 =
          let uu____59814 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes  in
          Prims.op_Hat uu____59814 "\""  in
        Prims.op_Hat "\"" uu____59812
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____59820 =
          let uu____59822 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.op_Hat uu____59822 "\""  in
        Prims.op_Hat "\"" uu____59820
    | uu____59826 ->
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
              let uu____59885 =
                let uu____59886 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____59886  in
              FStar_Format.parens uu____59885  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____59896 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____59902 =
                    let uu____59903 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____59903  in
                  FStar_Format.parens uu____59902
               in
            let name1 = ptsym currentModule name  in
            let uu____59907 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____59907
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____59909,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____59913 =
              let uu____59914 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____59914  in
            maybe_paren outer t_prio_fun uu____59913
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____59916 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____59916
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
        let uu____59928 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____59928

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
            let uu____60021 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____60021
            then
              let uu____60024 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1]
                 in
              FStar_Format.parens uu____60024
            else
              (let uu____60028 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____60028)
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
            let uu____60042 = FStar_Format.reduce docs1  in
            FStar_Format.parens uu____60042
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____60044 = string_of_mlconstant c  in
            FStar_Format.text uu____60044
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____60049 = ptsym currentModule path  in
            FStar_Format.text uu____60049
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____60083 =
              match uu____60083 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60094 =
                    let uu____60097 =
                      let uu____60098 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____60098  in
                    [uu____60097; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____60094
               in
            let uu____60105 =
              let uu____60106 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____60106  in
            FStar_Format.cbrackets uu____60105
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____60120 = is_standard_constructor ctor  in
              if uu____60120
              then
                let uu____60124 =
                  let uu____60131 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60131  in
                FStar_Pervasives_Native.snd uu____60124
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____60158 = is_standard_constructor ctor  in
              if uu____60158
              then
                let uu____60162 =
                  let uu____60169 = as_standard_constructor ctor  in
                  FStar_Option.get uu____60169  in
                FStar_Pervasives_Native.snd uu____60162
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
              | (uu____60202,uu____60203) ->
                  let uu____60210 =
                    let uu____60213 =
                      let uu____60216 =
                        let uu____60217 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____60217  in
                      [uu____60216]  in
                    (FStar_Format.text name) :: uu____60213  in
                  FStar_Format.reduce1 uu____60210
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____60228 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____60228) es
               in
            let docs1 =
              let uu____60230 =
                FStar_Format.combine (FStar_Format.text ", ") docs  in
              FStar_Format.parens uu____60230  in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____60247 =
                  let uu____60250 =
                    let uu____60253 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____60253]  in
                  FStar_Format.hardline :: uu____60250  in
                FStar_Format.reduce uu____60247
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____60262 =
              let uu____60263 =
                let uu____60266 =
                  let uu____60269 =
                    let uu____60272 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____60272]  in
                  doc1 :: uu____60269  in
                pre :: uu____60266  in
              FStar_Format.combine FStar_Format.hardline uu____60263  in
            FStar_Format.parens uu____60262
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____60283::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____60285;
                    FStar_Extraction_ML_Syntax.loc = uu____60286;_}::
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun
                    ((arg,uu____60288)::[],possible_match);
                  FStar_Extraction_ML_Syntax.mlty = uu____60290;
                  FStar_Extraction_ML_Syntax.loc = uu____60291;_}::[])
                 when
                 let uu____60335 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____60335 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____60361;
                            FStar_Extraction_ML_Syntax.loc = uu____60362;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____60364;
                       FStar_Extraction_ML_Syntax.loc = uu____60365;_} when
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60423;
                   FStar_Extraction_ML_Syntax.loc = uu____60424;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____60437;
                   FStar_Extraction_ML_Syntax.loc = uu____60438;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____60445 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____60456 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____60456)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____60461 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60461
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____60471 =
                   let uu____60474 =
                     let uu____60477 =
                       let uu____60480 =
                         let uu____60481 = ptsym currentModule f  in
                         FStar_Format.text uu____60481  in
                       [uu____60480]  in
                     (FStar_Format.text ".") :: uu____60477  in
                   e2 :: uu____60474  in
                 FStar_Format.reduce uu____60471)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____60517 = FStar_Extraction_ML_Util.codegen_fsharp ()
                 in
              if uu____60517
              then
                let uu____60520 =
                  let uu____60523 =
                    let uu____60526 =
                      let uu____60529 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____60531 =
                              let uu____60534 =
                                let uu____60537 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____60537]  in
                              (FStar_Format.text " : ") :: uu____60534  in
                            FStar_Format.reduce1 uu____60531
                        | uu____60539 -> FStar_Format.text ""  in
                      [uu____60529; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____60526  in
                  (FStar_Format.text "(") :: uu____60523  in
                FStar_Format.reduce1 uu____60520
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____60558  ->
                   match uu____60558 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____60570 =
                let uu____60573 =
                  let uu____60576 = FStar_Format.reduce1 ids1  in
                  [uu____60576; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____60573  in
              FStar_Format.reduce1 uu____60570  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60585 =
                let uu____60588 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60592 =
                  let uu____60595 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____60595; FStar_Format.text "end"]  in
                uu____60588 :: uu____60592  in
              FStar_Format.combine FStar_Format.hardline uu____60585  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____60604 =
                let uu____60607 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____60611 =
                  let uu____60614 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____60615 =
                    let uu____60618 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____60622 =
                      let uu____60625 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____60625; FStar_Format.text "end"]  in
                    uu____60618 :: uu____60622  in
                  uu____60614 :: uu____60615  in
                uu____60607 :: uu____60611  in
              FStar_Format.combine FStar_Format.hardline uu____60604  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____60664 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____60664 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____60671 =
              let uu____60674 =
                let uu____60677 =
                  let uu____60678 = ptctor currentModule exn  in
                  FStar_Format.text uu____60678  in
                [uu____60677]  in
              (FStar_Format.text "raise") :: uu____60674  in
            FStar_Format.reduce1 uu____60671
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____60690 =
              let uu____60693 =
                let uu____60696 =
                  let uu____60697 = ptctor currentModule exn  in
                  FStar_Format.text uu____60697  in
                let uu____60699 =
                  let uu____60702 =
                    let uu____60703 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____60703  in
                  [uu____60702]  in
                uu____60696 :: uu____60699  in
              (FStar_Format.text "raise") :: uu____60693  in
            FStar_Format.reduce1 uu____60690
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____60728 =
              let uu____60731 =
                let uu____60734 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____60735 =
                  let uu____60738 =
                    let uu____60741 =
                      let uu____60742 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____60742
                       in
                    [uu____60741]  in
                  (FStar_Format.text "with") :: uu____60738  in
                uu____60734 :: uu____60735  in
              (FStar_Format.text "try") :: uu____60731  in
            FStar_Format.combine FStar_Format.hardline uu____60728
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
          let uu____60766 =
            let uu____60780 = as_bin_op p  in FStar_Option.get uu____60780
             in
          match uu____60766 with
          | (uu____60809,prio,txt) ->
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
        let uu____60833 =
          let uu____60840 = as_uni_op p  in FStar_Option.get uu____60840  in
        match uu____60833 with
        | (uu____60855,txt) ->
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
          let uu____60868 = string_of_mlconstant c  in
          FStar_Format.text uu____60868
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____60904 =
            match uu____60904 with
            | (name,p) ->
                let uu____60914 =
                  let uu____60917 =
                    let uu____60918 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____60918  in
                  let uu____60924 =
                    let uu____60927 =
                      let uu____60930 = doc_of_pattern currentModule p  in
                      [uu____60930]  in
                    (FStar_Format.text "=") :: uu____60927  in
                  uu____60917 :: uu____60924  in
                FStar_Format.reduce1 uu____60914
             in
          let uu____60932 =
            let uu____60933 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____60933  in
          FStar_Format.cbrackets uu____60932
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____60947 = is_standard_constructor ctor  in
            if uu____60947
            then
              let uu____60951 =
                let uu____60958 = as_standard_constructor ctor  in
                FStar_Option.get uu____60958  in
              FStar_Pervasives_Native.snd uu____60951
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____60985 = is_standard_constructor ctor  in
            if uu____60985
            then
              let uu____60989 =
                let uu____60996 = as_standard_constructor ctor  in
                FStar_Option.get uu____60996  in
              FStar_Pervasives_Native.snd uu____60989
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____61025 =
                  let uu____61028 =
                    let uu____61029 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____61029  in
                  let uu____61030 =
                    let uu____61033 =
                      let uu____61036 = doc_of_pattern currentModule xs  in
                      [uu____61036]  in
                    (FStar_Format.text "::") :: uu____61033  in
                  uu____61028 :: uu____61030  in
                FStar_Format.reduce uu____61025
            | (uu____61038,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____61039)::[]) ->
                let uu____61046 =
                  let uu____61049 =
                    let uu____61052 =
                      let uu____61053 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____61053  in
                    [uu____61052]  in
                  (FStar_Format.text name) :: uu____61049  in
                FStar_Format.reduce1 uu____61046
            | uu____61054 ->
                let uu____61062 =
                  let uu____61065 =
                    let uu____61068 =
                      let uu____61069 =
                        let uu____61070 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____61070
                         in
                      FStar_Format.parens uu____61069  in
                    [uu____61068]  in
                  (FStar_Format.text name) :: uu____61065  in
                FStar_Format.reduce1 uu____61062
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____61085 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____61085
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2

and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61098  ->
      match uu____61098 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____61108 =
                  let uu____61111 =
                    let uu____61114 = doc_of_pattern currentModule p  in
                    [uu____61114]  in
                  (FStar_Format.text "|") :: uu____61111  in
                FStar_Format.reduce1 uu____61108
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____61118 =
                  let uu____61121 =
                    let uu____61124 = doc_of_pattern currentModule p  in
                    [uu____61124; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____61121  in
                FStar_Format.reduce1 uu____61118
             in
          let uu____61127 =
            let uu____61130 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____61133 =
              let uu____61136 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____61136; FStar_Format.text "end"]  in
            uu____61130 :: uu____61133  in
          FStar_Format.combine FStar_Format.hardline uu____61127

and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc)
  =
  fun currentModule  ->
    fun uu____61139  ->
      match uu____61139 with
      | (rec_,top_level,lets) ->
          let for1 uu____61164 =
            match uu____61164 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____61167;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu____61169;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____61185 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____61185
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____61188::uu____61189,uu____61190) ->
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
                                let uu____61214 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____61214
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____61233 =
                  let uu____61236 =
                    let uu____61239 = FStar_Format.reduce1 ids  in
                    [uu____61239; ty_annot; FStar_Format.text "="; e1]  in
                  (FStar_Format.text name) :: uu____61236  in
                FStar_Format.reduce1 uu____61233
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
  fun uu____61265  ->
    match uu____61265 with
    | (lineno,file) ->
        let uu____61272 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>")
           in
        if uu____61272
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
      let for1 uu____61324 =
        match uu____61324 with
        | (uu____61347,x,mangle_opt,tparams,uu____61351,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____61386 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams
                     in
                  let uu____61397 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____61397
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____61424 =
                    match uu____61424 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____61437 =
                    let uu____61438 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____61438
                     in
                  FStar_Format.cbrackets uu____61437
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____61479 =
                    match uu____61479 with
                    | (name,tys) ->
                        let uu____61510 = FStar_List.split tys  in
                        (match uu____61510 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____61533 ->
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
              let uu____61564 =
                let uu____61567 =
                  let uu____61570 =
                    let uu____61571 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____61571  in
                  [uu____61570]  in
                tparams1 :: uu____61567  in
              FStar_Format.reduce1 uu____61564  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____61580 =
                   let uu____61583 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____61583; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____61580)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____61591 =
            let uu____61594 =
              let uu____61597 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____61597]  in
            (FStar_Format.text "type") :: uu____61594  in
          FStar_Format.reduce1 uu____61591
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
          let uu____61633 =
            let uu____61636 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____61639 =
              let uu____61642 = doc_of_sig currentModule subsig  in
              let uu____61643 =
                let uu____61646 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____61646]  in
              uu____61642 :: uu____61643  in
            uu____61636 :: uu____61639  in
          FStar_Format.combine FStar_Format.hardline uu____61633
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____61666 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____61666  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____61671,ty)) ->
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
            let uu____61750 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____61750  in
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
          let uu____61766 =
            let uu____61769 =
              let uu____61772 =
                let uu____61775 =
                  let uu____61778 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____61778]  in
                (FStar_Format.text "=") :: uu____61775  in
              (FStar_Format.text "_") :: uu____61772  in
            (FStar_Format.text "let") :: uu____61769  in
          FStar_Format.reduce1 uu____61766
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
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____61808 ->
                  FStar_Format.empty
              | uu____61809 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list)
  =
  fun uu____61822  ->
    match uu____61822 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____61892 =
          match uu____61892 with
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
                  (fun uu____61952  ->
                     match uu____61952 with
                     | (s,uu____61958) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____61979 =
                let uu____61982 =
                  let uu____61985 =
                    let uu____61988 = FStar_Format.reduce sub3  in
                    [uu____61988;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____61985
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____61982
                 in
              FStar_Format.reduce uu____61979
        
        and for1_mod istop uu____61991 =
          match uu____61991 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1  in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____62073 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.op_Hat "open " pervasives1)]
                 in
              let head1 =
                let uu____62094 =
                  let uu____62097 =
                    FStar_Extraction_ML_Util.codegen_fsharp ()  in
                  if uu____62097
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
                FStar_Format.reduce1 uu____62094  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____62128  ->
                     match uu____62128 with
                     | (uu____62133,m) -> doc_of_mod target_mod_name m)
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
                let uu____62159 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____62159
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____62167 =
                let uu____62170 =
                  let uu____62173 =
                    let uu____62176 =
                      let uu____62179 =
                        let uu____62182 =
                          let uu____62185 = FStar_Format.reduce sub3  in
                          [uu____62185;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____62182
                         in
                      FStar_Format.hardline :: uu____62179  in
                    FStar_List.append maybe_open_pervasives uu____62176  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____62173
                   in
                FStar_List.append prefix1 uu____62170  in
              FStar_All.pipe_left FStar_Format.reduce uu____62167
         in
        let docs =
          FStar_List.map
            (fun uu____62229  ->
               match uu____62229 with
               | (x,s,m) ->
                   let uu____62286 =
                     FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let uu____62288 = for1_mod true (x, s, m)  in
                   (uu____62286, uu____62288)) mllib
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
        let uu____62331 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____62331 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____62347 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____62347 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  