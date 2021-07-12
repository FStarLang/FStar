open Prims
type assoc =
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_ILeft : assoc -> Prims.bool) =
  fun projectee -> match projectee with | ILeft -> true | uu___ -> false
let (uu___is_IRight : assoc -> Prims.bool) =
  fun projectee -> match projectee with | IRight -> true | uu___ -> false
let (uu___is_Left : assoc -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu___ -> false
let (uu___is_Right : assoc -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu___ -> false
let (uu___is_NonAssoc : assoc -> Prims.bool) =
  fun projectee -> match projectee with | NonAssoc -> true | uu___ -> false
type fixity =
  | Prefix 
  | Postfix 
  | Infix of assoc 
let (uu___is_Prefix : fixity -> Prims.bool) =
  fun projectee -> match projectee with | Prefix -> true | uu___ -> false
let (uu___is_Postfix : fixity -> Prims.bool) =
  fun projectee -> match projectee with | Postfix -> true | uu___ -> false
let (uu___is_Infix : fixity -> Prims.bool) =
  fun projectee -> match projectee with | Infix _0 -> true | uu___ -> false
let (__proj__Infix__item___0 : fixity -> assoc) =
  fun projectee -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int * fixity)
type level = (opprec * assoc)
let (t_prio_fun : (Prims.int * fixity)) =
  ((Prims.of_int (10)), (Infix Right))
let (t_prio_tpl : (Prims.int * fixity)) =
  ((Prims.of_int (20)), (Infix NonAssoc))
let (t_prio_name : (Prims.int * fixity)) = ((Prims.of_int (30)), Postfix)
let (e_bin_prio_lambda : (Prims.int * fixity)) = ((Prims.of_int (5)), Prefix)
let (e_bin_prio_if : (Prims.int * fixity)) = ((Prims.of_int (15)), Prefix)
let (e_bin_prio_letin : (Prims.int * fixity)) = ((Prims.of_int (19)), Prefix)
let (e_bin_prio_or : (Prims.int * fixity)) =
  ((Prims.of_int (20)), (Infix Left))
let (e_bin_prio_and : (Prims.int * fixity)) =
  ((Prims.of_int (25)), (Infix Left))
let (e_bin_prio_eq : (Prims.int * fixity)) =
  ((Prims.of_int (27)), (Infix NonAssoc))
let (e_bin_prio_order : (Prims.int * fixity)) =
  ((Prims.of_int (29)), (Infix NonAssoc))
let (e_bin_prio_op1 : (Prims.int * fixity)) =
  ((Prims.of_int (30)), (Infix Left))
let (e_bin_prio_op2 : (Prims.int * fixity)) =
  ((Prims.of_int (40)), (Infix Left))
let (e_bin_prio_op3 : (Prims.int * fixity)) =
  ((Prims.of_int (50)), (Infix Left))
let (e_bin_prio_op4 : (Prims.int * fixity)) =
  ((Prims.of_int (60)), (Infix Left))
let (e_bin_prio_comb : (Prims.int * fixity)) =
  ((Prims.of_int (70)), (Infix Left))
let (e_bin_prio_seq : (Prims.int * fixity)) =
  ((Prims.of_int (100)), (Infix Left))
let (e_app_prio : (Prims.int * fixity)) =
  ((Prims.of_int (10000)), (Infix Left))
let (min_op_prec : (Prims.int * fixity)) =
  ((~- Prims.int_one), (Infix NonAssoc))
let (max_op_prec : (Prims.int * fixity)) =
  (FStar_Util.max_int, (Infix NonAssoc))
type doc =
  | Doc of Prims.string 
let (uu___is_Doc : doc -> Prims.bool) = fun projectee -> true
let (__proj__Doc__item___0 : doc -> Prims.string) =
  fun projectee -> match projectee with | Doc _0 -> _0
let (empty : doc) = Doc ""
let (hardline : doc) = Doc "\n"
let (text : Prims.string -> doc) = fun s -> Doc s
let (num : Prims.int -> doc) =
  fun i -> let uu___ = FStar_Util.string_of_int i in Doc uu___
let (break1 : doc) = text " "
let (enclose : doc -> doc -> doc -> doc) =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        match (uu___, uu___1, uu___2) with
        | (Doc l, Doc r, Doc x) -> Doc (Prims.op_Hat l (Prims.op_Hat x r))
let (cbrackets : doc -> doc) =
  fun uu___ ->
    match uu___ with | Doc d -> enclose (text "{") (text "}") (Doc d)
let (parens : doc -> doc) =
  fun uu___ ->
    match uu___ with | Doc d -> enclose (text "(") (text ")") (Doc d)
let (cat : doc -> doc -> doc) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | (Doc d1, Doc d2) -> Doc (Prims.op_Hat d1 d2)
let (reduce : doc Prims.list -> doc) =
  fun docs -> FStar_List.fold_left cat empty docs
let (combine : doc -> doc Prims.list -> doc) =
  fun uu___ ->
    fun docs ->
      match uu___ with
      | Doc sep ->
          let select uu___1 =
            match uu___1 with
            | Doc d ->
                if d = ""
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some d in
          let docs1 = FStar_List.choose select docs in
          Doc (FStar_String.concat sep docs1)
let (reduce1 : doc Prims.list -> doc) = fun docs -> combine break1 docs
let (hbox : doc -> doc) = fun d -> d
let rec in_ns : 'a . ('a Prims.list * 'a Prims.list) -> Prims.bool =
  fun x ->
    match x with
    | ([], uu___) -> true
    | (x1::t1, x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu___, uu___1) -> false
let (path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list)
  =
  fun currentModule ->
    fun ns ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns in
      if ns' = currentModule
      then []
      else
        (let cg_libs = FStar_Options.codegen_libs () in
         let ns_len = FStar_List.length ns in
         let found =
           FStar_Util.find_map cg_libs
             (fun cg_path ->
                let cg_len = FStar_List.length cg_path in
                if (FStar_List.length cg_path) < ns_len
                then
                  let uu___1 = FStar_Util.first_N cg_len ns in
                  match uu___1 with
                  | (pfx, sfx) ->
                      (if pfx = cg_path
                       then
                         let uu___2 =
                           let uu___3 =
                             let uu___4 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu___4] in
                           FStar_List.append pfx uu___3 in
                         FStar_Pervasives_Native.Some uu___2
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None) in
         match found with
         | FStar_Pervasives_Native.None -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
let (mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath)
  =
  fun currentModule ->
    fun x ->
      let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu___ with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu___1 ->
          let uu___2 = x in
          (match uu___2 with
           | (ns, x1) ->
               let uu___3 = path_of_ns currentModule ns in (uu___3, x1))
let (ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun s ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_String.get s Prims.int_zero in
        FStar_Char.lowercase uu___2 in
      let uu___2 = FStar_String.get s Prims.int_zero in uu___1 <> uu___2 in
    if uu___ then Prims.op_Hat "l__" s else s
let (ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule ->
    fun mlp ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu___1 = mlpath_of_mlpath currentModule mlp in
         match uu___1 with
         | (p, s) ->
             let uu___2 =
               let uu___3 = let uu___4 = ptsym_of_symbol s in [uu___4] in
               FStar_List.append p uu___3 in
             FStar_String.concat "." uu___2)
let (ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)
  =
  fun currentModule ->
    fun mlp ->
      let uu___ = mlpath_of_mlpath currentModule mlp in
      match uu___ with
      | (p, s) ->
          let s1 =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_String.get s Prims.int_zero in
                FStar_Char.uppercase uu___3 in
              let uu___3 = FStar_String.get s Prims.int_zero in
              uu___2 <> uu___3 in
            if uu___1 then Prims.op_Hat "U__" s else s in
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
  fun uu___ ->
    let op_minus =
      let uu___1 =
        let uu___2 = FStar_Options.codegen () in
        uu___2 = (FStar_Pervasives_Native.Some FStar_Options.FSharp) in
      if uu___1 then "-" else "~-" in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
let prim_types : 'uuuuu . unit -> 'uuuuu Prims.list = fun uu___ -> []
let (prim_constructors : (Prims.string * Prims.string) Prims.list) =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let (is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool) =
  fun ns -> ns = ["Prims"]
let (as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) *
      Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (ns, x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu___1 -> match uu___1 with | (y, uu___2, uu___3) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let (is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p -> let uu___ = as_bin_op p in uu___ <> FStar_Pervasives_Native.None
let (as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (ns, x) ->
        if is_prims_ns ns
        then
          let uu___1 = prim_uni_ops () in
          FStar_List.tryFind
            (fun uu___2 -> match uu___2 with | (y, uu___3) -> x = y) uu___1
        else FStar_Pervasives_Native.None
let (is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p -> let uu___ = as_uni_op p in uu___ <> FStar_Pervasives_Native.None
let (is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p -> false
let (as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string)
      FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (ns, x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu___1 -> match uu___1 with | (y, uu___2) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let (is_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath -> Prims.bool) =
  fun p ->
    let uu___ = as_standard_constructor p in
    uu___ <> FStar_Pervasives_Native.None
let (maybe_paren :
  ((Prims.int * fixity) * assoc) -> (Prims.int * fixity) -> doc -> doc) =
  fun uu___ ->
    fun inner ->
      fun doc1 ->
        match uu___ with
        | (outer, side) ->
            let noparens _inner _outer side1 =
              let uu___1 = _inner in
              match uu___1 with
              | (pi, fi) ->
                  let uu___2 = _outer in
                  (match uu___2 with
                   | (po, fo) ->
                       (pi > po) ||
                         ((match (fi, side1) with
                           | (Postfix, Left) -> true
                           | (Prefix, Right) -> true
                           | (Infix (Left), Left) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right), Right) ->
                               (pi = po) && (fo = (Infix Right))
                           | (Infix (Left), ILeft) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right), IRight) ->
                               (pi = po) && (fo = (Infix Right))
                           | (uu___3, NonAssoc) -> (pi = po) && (fi = fo)
                           | (uu___3, uu___4) -> false))) in
            if noparens inner outer side then doc1 else parens doc1
let (escape_byte_hex : FStar_BaseTypes.byte -> Prims.string) =
  fun x -> Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x)
let (escape_char_hex : FStar_BaseTypes.char -> Prims.string) =
  fun x -> escape_byte_hex (FStar_Util.byte_of_char x)
let (escape_or :
  (FStar_BaseTypes.char -> Prims.string) ->
    FStar_BaseTypes.char -> Prims.string)
  =
  fun fallback ->
    fun uu___ ->
      if uu___ = 92
      then "\\\\"
      else
        if uu___ = 32
        then " "
        else
          if uu___ = 8
          then "\\b"
          else
            if uu___ = 9
            then "\\t"
            else
              if uu___ = 13
              then "\\r"
              else
                if uu___ = 10
                then "\\n"
                else
                  if uu___ = 39
                  then "\\'"
                  else
                    if uu___ = 34
                    then "\\\""
                    else
                      if FStar_Util.is_letter_or_digit uu___
                      then FStar_Util.string_of_char uu___
                      else
                        if FStar_Util.is_punctuation uu___
                        then FStar_Util.string_of_char uu___
                        else
                          if FStar_Util.is_symbol uu___
                          then FStar_Util.string_of_char uu___
                          else fallback uu___
let (string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string) =
  fun sctt ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c in
        let uu___ = FStar_Util.string_of_int nc in
        Prims.op_Hat uu___
          (if
             ((nc >= (Prims.of_int (32))) && (nc <= (Prims.of_int (127)))) &&
               (nc <> (Prims.of_int (34)))
           then
             Prims.op_Hat " (*"
               (Prims.op_Hat (FStar_Util.string_of_char c) "*)")
           else "")
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some
         (FStar_Const.Signed, FStar_Const.Int32))
        -> Prims.op_Hat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some
         (FStar_Const.Signed, FStar_Const.Int64))
        -> Prims.op_Hat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some (uu___, FStar_Const.Int8)) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some (uu___, FStar_Const.Int16)) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (v, FStar_Pervasives_Native.Some (s, w)) ->
        let sign =
          match s with
          | FStar_Const.Signed -> "Int"
          | FStar_Const.Unsigned -> "UInt" in
        let ws =
          match w with
          | FStar_Const.Int8 -> "8"
          | FStar_Const.Int16 -> "16"
          | FStar_Const.Int32 -> "32"
          | FStar_Const.Int64 -> "64" in
        let z = Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat v "\")") in
        let u =
          match s with
          | FStar_Const.Signed -> ""
          | FStar_Const.Unsigned -> "u" in
        Prims.op_Hat "(FStar_"
          (Prims.op_Hat sign
             (Prims.op_Hat ws
                (Prims.op_Hat "."
                   (Prims.op_Hat u
                      (Prims.op_Hat "int_to_t (" (Prims.op_Hat z "))"))))))
    | FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) ->
        Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu___ =
          let uu___1 = FStar_Compiler_Bytes.f_encode escape_byte_hex bytes in
          Prims.op_Hat uu___1 "\"" in
        Prims.op_Hat "\"" uu___
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu___ =
          let uu___1 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.op_Hat uu___1 "\"" in
        Prims.op_Hat "\"" uu___
    | uu___ -> failwith "TODO: extract integer constants properly into OCaml"
let rec (doc_of_mltype' :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule ->
    fun outer ->
      fun ty ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s 95 117
              else s in
            text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu___ =
                let uu___1 = combine (text " * ") doc1 in hbox uu___1 in
              parens uu___ in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args, name) ->
            let args1 =
              match args with
              | [] -> empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu___ ->
                  let args2 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu___1 =
                    let uu___2 = combine (text ", ") args2 in hbox uu___2 in
                  parens uu___1 in
            let name1 = ptsym currentModule name in
            let uu___ = reduce1 [args1; text name1] in hbox uu___
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu___1 =
              let uu___2 = reduce1 [d1; text " -> "; d2] in hbox uu___2 in
            maybe_paren outer t_prio_fun uu___1
        | FStar_Extraction_ML_Syntax.MLTY_Top ->
            let uu___ = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu___ then text "obj" else text "Obj.t"
        | FStar_Extraction_ML_Syntax.MLTY_Erased -> text "unit"
and (doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> doc)
  =
  fun currentModule ->
    fun outer ->
      fun ty ->
        let uu___ = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu___
let rec (doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule ->
    fun outer ->
      fun e ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let uu___ = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu___
            then
              let uu___1 = reduce [text "Prims.unsafe_coerce "; doc1] in
              parens uu___1
            else
              (let uu___2 = reduce [text "Obj.magic "; parens doc1] in
               parens uu___2)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs1 =
              FStar_List.map (fun d -> reduce [d; text ";"; hardline]) docs in
            let uu___ = reduce docs1 in parens uu___
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu___ = string_of_mlconstant c in text uu___
        | FStar_Extraction_ML_Syntax.MLE_Var x -> text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu___ = ptsym currentModule path in text uu___
        | FStar_Extraction_ML_Syntax.MLE_Record (path, fields) ->
            let for1 uu___ =
              match uu___ with
              | (name, e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = ptsym currentModule (path, name) in
                      text uu___3 in
                    [uu___2; text "="; doc1] in
                  reduce1 uu___1 in
            let uu___ =
              let uu___1 = FStar_List.map for1 fields in
              combine (text "; ") uu___1 in
            cbrackets uu___
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) ->
            let name =
              let uu___ = is_standard_constructor ctor in
              if uu___
              then
                let uu___1 =
                  let uu___2 = as_standard_constructor ctor in
                  FStar_Option.get uu___2 in
                FStar_Pervasives_Native.snd uu___1
              else ptctor currentModule ctor in
            text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) ->
            let name =
              let uu___ = is_standard_constructor ctor in
              if uu___
              then
                let uu___1 =
                  let uu___2 = as_standard_constructor ctor in
                  FStar_Option.get uu___2 in
                FStar_Pervasives_Native.snd uu___1
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::", x::xs::[]) -> reduce [parens x; text "::"; xs]
              | (uu___, uu___1) ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = combine (text ", ") args1 in
                        parens uu___5 in
                      [uu___4] in
                    (text name) :: uu___3 in
                  reduce1 uu___2 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x ->
                   let uu___ =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   parens uu___) es in
            let docs1 = let uu___ = combine (text ", ") docs in parens uu___ in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu___ =
                  let uu___1 =
                    let uu___2 = doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu___2] in
                  hardline :: uu___1 in
                reduce uu___
              else empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 = reduce1 [text "in"; body1] in [uu___4] in
                  doc1 :: uu___3 in
                pre :: uu___2 in
              combine hardline uu___1 in
            parens uu___
        | FStar_Extraction_ML_Syntax.MLE_App (e1, args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name p,
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun (uu___::[], scrutinee);
                  FStar_Extraction_ML_Syntax.mlty = uu___1;
                  FStar_Extraction_ML_Syntax.loc = uu___2;_}::{
                                                                FStar_Extraction_ML_Syntax.expr
                                                                  =
                                                                  FStar_Extraction_ML_Syntax.MLE_Fun
                                                                  ((arg,
                                                                    uu___3)::[],
                                                                   possible_match);
                                                                FStar_Extraction_ML_Syntax.mlty
                                                                  = uu___4;
                                                                FStar_Extraction_ML_Syntax.loc
                                                                  = uu___5;_}::[])
                 when
                 let uu___6 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu___6 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu___6;
                            FStar_Extraction_ML_Syntax.loc = uu___7;_},
                          branches1);
                       FStar_Extraction_ML_Syntax.mlty = uu___8;
                       FStar_Extraction_ML_Syntax.loc = uu___9;_} when
                       arg = arg' -> branches1
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
             | (FStar_Extraction_ML_Syntax.MLE_Name p, e11::e2::[]) when
                 is_bin_op p -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu___;
                   FStar_Extraction_ML_Syntax.loc = uu___1;_},
                 unitVal::[]),
                e11::e2::[]) when
                 (is_bin_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_Name p, e11::[]) when
                 is_uni_op p -> doc_of_uniop currentModule p e11
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu___;
                   FStar_Extraction_ML_Syntax.loc = uu___1;_},
                 unitVal::[]),
                e11::[]) when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu___ ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu___1 = reduce1 (e2 :: args1) in parens uu___1)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu___ = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu___
              then
                reduce [e2; text "."; text (FStar_Pervasives_Native.snd f)]
              else
                (let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = ptsym currentModule f in text uu___6 in
                       [uu___5] in
                     (text ".") :: uu___4 in
                   e2 :: uu___3 in
                 reduce uu___2) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) ->
            let bvar_annot x xt =
              let uu___ = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu___
              then
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu___7] in
                              (text " : ") :: uu___6 in
                            reduce1 uu___5
                        | uu___5 -> text "" in
                      [uu___4; text ")"] in
                    (text x) :: uu___3 in
                  (text "(") :: uu___2 in
                reduce1 uu___1
              else text x in
            let ids1 =
              FStar_List.map
                (fun uu___ ->
                   match uu___ with
                   | (x, xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu___ =
                let uu___1 =
                  let uu___2 = reduce1 ids1 in [uu___2; text "->"; body1] in
                (text "fun") :: uu___1 in
              reduce1 uu___ in
            parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond, e1, FStar_Pervasives_Native.None) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu___ =
                let uu___1 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"] in
                let uu___2 =
                  let uu___3 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu___3; text "end"] in
                uu___1 :: uu___2 in
              combine hardline uu___ in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond, e1, FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu___ =
                let uu___1 =
                  reduce1 [text "if"; cond1; text "then"; text "begin"] in
                let uu___2 =
                  let uu___3 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu___4 =
                    let uu___5 =
                      reduce1 [text "end"; text "else"; text "begin"] in
                    let uu___6 =
                      let uu___7 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu___7; text "end"] in
                    uu___5 :: uu___6 in
                  uu___3 :: uu___4 in
                uu___1 :: uu___2 in
              combine hardline uu___ in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu___ = reduce1 [text "match"; parens cond1; text "with"] in
              uu___ :: pats1 in
            let doc2 = combine hardline doc1 in parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = ptctor currentModule exn in text uu___3 in
                [uu___2] in
              (text "raise") :: uu___1 in
            reduce1 uu___
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = ptctor currentModule exn in text uu___3 in
                let uu___3 =
                  let uu___4 =
                    let uu___5 = combine (text ", ") args1 in parens uu___5 in
                  [uu___4] in
                uu___2 :: uu___3 in
              (text "raise") :: uu___1 in
            reduce1 uu___
        | FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      combine hardline uu___6 in
                    [uu___5] in
                  (text "with") :: uu___4 in
                uu___2 :: uu___3 in
              (text "try") :: uu___1 in
            combine hardline uu___
        | FStar_Extraction_ML_Syntax.MLE_TApp (head, ty_args) ->
            doc_of_expr currentModule outer head
and (doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule ->
    fun p ->
      fun e1 ->
        fun e2 ->
          let uu___ = let uu___1 = as_bin_op p in FStar_Option.get uu___1 in
          match uu___ with
          | (uu___1, prio, txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1 in
              let e21 = doc_of_expr currentModule (prio, Right) e2 in
              let doc1 = reduce1 [e11; text txt; e21] in parens doc1
and (doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> doc)
  =
  fun currentModule ->
    fun p ->
      fun e1 ->
        let uu___ = let uu___1 = as_uni_op p in FStar_Option.get uu___1 in
        match uu___ with
        | (uu___1, txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 = reduce1 [text txt; parens e11] in parens doc1
and (doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> doc)
  =
  fun currentModule ->
    fun pattern ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild -> text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu___ = string_of_mlconstant c in text uu___
      | FStar_Extraction_ML_Syntax.MLP_Var x -> text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path, fields) ->
          let for1 uu___ =
            match uu___ with
            | (name, p) ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 = ptsym currentModule (path, name) in
                    text uu___3 in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = doc_of_pattern currentModule p in [uu___5] in
                    (text "=") :: uu___4 in
                  uu___2 :: uu___3 in
                reduce1 uu___1 in
          let uu___ =
            let uu___1 = FStar_List.map for1 fields in
            combine (text "; ") uu___1 in
          cbrackets uu___
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) ->
          let name =
            let uu___ = is_standard_constructor ctor in
            if uu___
            then
              let uu___1 =
                let uu___2 = as_standard_constructor ctor in
                FStar_Option.get uu___2 in
              FStar_Pervasives_Native.snd uu___1
            else ptctor currentModule ctor in
          text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) ->
          let name =
            let uu___ = is_standard_constructor ctor in
            if uu___
            then
              let uu___1 =
                let uu___2 = as_standard_constructor ctor in
                FStar_Option.get uu___2 in
              FStar_Pervasives_Native.snd uu___1
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::", x::xs::[]) ->
                let uu___ =
                  let uu___1 =
                    let uu___2 = doc_of_pattern currentModule x in
                    parens uu___2 in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = doc_of_pattern currentModule xs in
                      [uu___4] in
                    (text "::") :: uu___3 in
                  uu___1 :: uu___2 in
                reduce uu___
            | (uu___, (FStar_Extraction_ML_Syntax.MLP_Tuple uu___1)::[]) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu___5 in
                    [uu___4] in
                  (text name) :: uu___3 in
                reduce1 uu___2
            | uu___ ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        combine (text ", ") uu___5 in
                      parens uu___4 in
                    [uu___3] in
                  (text name) :: uu___2 in
                reduce1 uu___1 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu___ = combine (text ", ") ps1 in parens uu___
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map parens ps1 in combine (text " | ") ps2
and (doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> doc)
  =
  fun currentModule ->
    fun uu___ ->
      match uu___ with
      | (p, cond, e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 = doc_of_pattern currentModule p in [uu___3] in
                  (text "|") :: uu___2 in
                reduce1 uu___1
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu___1 =
                  let uu___2 =
                    let uu___3 = doc_of_pattern currentModule p in
                    [uu___3; text "when"; c1] in
                  (text "|") :: uu___2 in
                reduce1 uu___1 in
          let uu___1 =
            let uu___2 = reduce1 [case; text "->"; text "begin"] in
            let uu___3 =
              let uu___4 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu___4; text "end"] in
            uu___2 :: uu___3 in
          combine hardline uu___1
and (doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> doc)
  =
  fun currentModule ->
    fun uu___ ->
      match uu___ with
      | (rec_, top_level, lets) ->
          let for1 uu___1 =
            match uu___1 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu___2;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.mllb_meta = uu___3;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then text ""
                  else
                    (let uu___5 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu___5
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu___6::uu___7, uu___8) -> text ""
                       | FStar_Pervasives_Native.None -> text ""
                       | FStar_Pervasives_Native.Some ([], ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           reduce1 [text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | FStar_Pervasives_Native.None -> text ""
                          | FStar_Pervasives_Native.Some ([], ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              reduce1 [text ":"; ty1]
                          | FStar_Pervasives_Native.Some (vs, ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              let vars =
                                let uu___7 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu___7 reduce1 in
                              reduce1 [text ":"; vars; text "."; ty1])
                       else text "") in
                let uu___4 =
                  let uu___5 =
                    let uu___6 = reduce1 ids in
                    [uu___6; ty_annot; text "="; e1] in
                  (text name) :: uu___5 in
                reduce1 uu___4 in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then reduce1 [text "let"; text "rec"]
            else text "let" in
          let lets1 = FStar_List.map for1 lets in
          let lets2 =
            FStar_List.mapi
              (fun i ->
                 fun doc1 ->
                   reduce1
                     [if i = Prims.int_zero then letdoc else text "and";
                     doc1]) lets1 in
          combine hardline lets2
and (doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> doc) =
  fun uu___ ->
    match uu___ with
    | (lineno, file) ->
        let uu___1 =
          ((FStar_Options.no_location_info ()) ||
             (FStar_Extraction_ML_Util.codegen_fsharp ()))
            || (file = "<dummy>") in
        if uu___1
        then empty
        else
          (let file1 = FStar_Util.basename file in
           let uu___3 =
             let uu___4 =
               let uu___5 = num lineno in
               [uu___5; text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))] in
             (text "#") :: uu___4 in
           reduce1 uu___3)
let (doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> doc)
  =
  fun currentModule ->
    fun decls ->
      let for1 uu___ =
        match uu___ with
        | { FStar_Extraction_ML_Syntax.tydecl_assumed = uu___1;
            FStar_Extraction_ML_Syntax.tydecl_name = x;
            FStar_Extraction_ML_Syntax.tydecl_ignored = mangle_opt;
            FStar_Extraction_ML_Syntax.tydecl_parameters = tparams;
            FStar_Extraction_ML_Syntax.tydecl_meta = uu___2;
            FStar_Extraction_ML_Syntax.tydecl_defn = body;_} ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> empty
              | x2::[] -> text x2
              | uu___3 ->
                  let doc1 = FStar_List.map (fun x2 -> text x2) tparams in
                  let uu___4 = combine (text ", ") doc1 in parens uu___4 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu___3 =
                    match uu___3 with
                    | (name, ty) ->
                        let name1 = text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        reduce1 [name1; text ":"; ty1] in
                  let uu___3 =
                    let uu___4 = FStar_List.map forfield fields in
                    combine (text "; ") uu___4 in
                  cbrackets uu___3
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu___3 =
                    match uu___3 with
                    | (name, tys) ->
                        let uu___4 = FStar_List.split tys in
                        (match uu___4 with
                         | (_names, tys1) ->
                             (match tys1 with
                              | [] -> text name
                              | uu___5 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1 in
                                  let tys3 = combine (text " * ") tys2 in
                                  reduce1 [text name; text "of"; tys3])) in
                  let ctors1 = FStar_List.map forctor ctors in
                  let ctors2 =
                    FStar_List.map (fun d -> reduce1 [text "|"; d]) ctors1 in
                  combine hardline ctors2 in
            let doc1 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = ptsym currentModule ([], x1) in text uu___6 in
                  [uu___5] in
                tparams1 :: uu___4 in
              reduce1 uu___3 in
            (match body with
             | FStar_Pervasives_Native.None -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu___3 =
                   let uu___4 = reduce1 [doc1; text "="] in [uu___4; body2] in
                 combine hardline uu___3) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > Prims.int_zero
        then
          let uu___ =
            let uu___1 =
              let uu___2 = combine (text " \n and ") doc1 in [uu___2] in
            (text "type") :: uu___1 in
          reduce1 uu___
        else text "" in
      doc2
let rec (doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> doc)
  =
  fun currentModule ->
    fun s ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) ->
          let uu___ =
            let uu___1 = reduce1 [text "module"; text x; text "="] in
            let uu___2 =
              let uu___3 = doc_of_sig currentModule subsig in
              let uu___4 = let uu___5 = reduce1 [text "end"] in [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          combine hardline uu___
      | FStar_Extraction_ML_Syntax.MLS_Exn (x, []) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x, args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 = let uu___ = combine (text " * ") args1 in parens uu___ in
          reduce1 [text "exception"; text x; text "of"; args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x, (uu___, ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          reduce1 [text "val"; text x; text ": "; ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and (doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> doc)
  =
  fun currentModule ->
    fun s ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs1 =
        FStar_List.map (fun x -> reduce [x; hardline; hardline]) docs in
      reduce docs1
let (doc_of_mod1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> doc)
  =
  fun currentModule ->
    fun m ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x, []) ->
          reduce1 [text "exception"; text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x, args) ->
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1 in
          let args3 = let uu___ = combine (text " * ") args2 in parens uu___ in
          reduce1 [text "exception"; text x; text "of"; args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu___4] in
                (text "=") :: uu___3 in
              (text "_") :: uu___2 in
            (text "let") :: uu___1 in
          reduce1 uu___
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let (doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> doc)
  =
  fun currentModule ->
    fun m ->
      let docs =
        FStar_List.map
          (fun x ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> empty
              | uu___ -> hardline);
             hardline]) m in
      reduce (FStar_List.flatten docs)
let (doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu___1 =
          match uu___1 with
          | (x, sigmod, FStar_Extraction_ML_Syntax.MLLib sub) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head =
                reduce1 [text "module"; text x1; text ":"; text "sig"] in
              let tail = reduce1 [text "end"] in
              let doc1 =
                FStar_Option.map
                  (fun uu___2 ->
                     match uu___2 with | (s, uu___3) -> doc_of_sig x1 s)
                  sigmod in
              let sub1 = FStar_List.map for1_sig sub in
              let sub2 =
                FStar_List.map (fun x2 -> reduce [x2; hardline; hardline])
                  sub1 in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = reduce sub2 in [uu___5; cat tail hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None -> empty
                   | FStar_Pervasives_Native.Some s -> cat s hardline) ::
                    uu___4 in
                (cat head hardline) :: uu___3 in
              reduce uu___2
        and for1_mod istop uu___1 =
          match uu___1 with
          | (mod_name, sigmod, FStar_Extraction_ML_Syntax.MLLib sub) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[], "Pervasives") -> []
                | uu___2 ->
                    let pervasives =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [hardline; text (Prims.op_Hat "open " pervasives)] in
              let head =
                let uu___2 =
                  let uu___3 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu___3
                  then [text "module"; text target_mod_name]
                  else
                    if Prims.op_Negation istop
                    then
                      [text "module";
                      text target_mod_name;
                      text "=";
                      text "struct"]
                    else [] in
                reduce1 uu___2 in
              let tail =
                if Prims.op_Negation istop
                then reduce1 [text "end"]
                else reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu___2 ->
                     match uu___2 with
                     | (uu___3, m) -> doc_of_mod target_mod_name m) sigmod in
              let sub1 = FStar_List.map (for1_mod false) sub in
              let sub2 =
                FStar_List.map (fun x -> reduce [x; hardline; hardline]) sub1 in
              let prefix =
                let uu___2 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu___2 then [cat (text "#light \"off\"") hardline] else [] in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = reduce sub2 in
                          [uu___8; cat tail hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None -> empty
                         | FStar_Pervasives_Native.Some s -> cat s hardline)
                          :: uu___7 in
                      hardline :: uu___6 in
                    FStar_List.append maybe_open_pervasives uu___5 in
                  FStar_List.append [head; hardline; text "open Prims"]
                    uu___4 in
                FStar_List.append prefix uu___3 in
              FStar_All.pipe_left reduce uu___2 in
        let docs =
          FStar_List.map
            (fun uu___1 ->
               match uu___1 with
               | (x, s, m) ->
                   let uu___2 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu___3 = for1_mod true (x, s, m) in (uu___2, uu___3))
            mllib in
        docs
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz -> fun uu___ -> match uu___ with | Doc doc1 -> doc1
let (doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib -> (Prims.string * doc) Prims.list) =
  fun mllib -> doc_of_mllib_r mllib
let (string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)
  =
  fun cmod ->
    fun e ->
      let doc1 =
        let uu___ = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu___ (min_op_prec, NonAssoc) e in
      pretty Prims.int_zero doc1
let (string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string)
  =
  fun cmod ->
    fun e ->
      let doc1 =
        let uu___ = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu___ (min_op_prec, NonAssoc) e in
      pretty Prims.int_zero doc1