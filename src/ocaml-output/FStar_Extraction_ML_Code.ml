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
                         Some
                           (let _0_217 =
                              let _0_216 =
                                FStar_Extraction_ML_Util.flatten_ns sfx in
                              [_0_216] in
                            FStar_List.append pfx _0_217)
                       else None)
                else None) in
         match found with | None  -> [ns'] | Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____188 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____188 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____191 ->
          let uu____192 = x in
          (match uu____192 with
           | (ns,x) ->
               let _0_218 = path_of_ns currentModule ns in (_0_218, x))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____201 =
      let _0_220 =
        FStar_Char.lowercase (FStar_String.get s (Prims.parse_int "0")) in
      let _0_219 = FStar_String.get s (Prims.parse_int "0") in
      _0_220 <> _0_219 in
    if uu____201 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (Prims.fst mlp)
      then ptsym_of_symbol (Prims.snd mlp)
      else
        (let uu____212 = mlpath_of_mlpath currentModule mlp in
         match uu____212 with
         | (p,s) ->
             let _0_223 =
               let _0_222 = let _0_221 = ptsym_of_symbol s in [_0_221] in
               FStar_List.append p _0_222 in
             FStar_String.concat "." _0_223)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____223 = mlpath_of_mlpath currentModule mlp in
      match uu____223 with
      | (p,s) ->
          let s =
            let uu____229 =
              let _0_225 =
                FStar_Char.uppercase
                  (FStar_String.get s (Prims.parse_int "0")) in
              let _0_224 = FStar_String.get s (Prims.parse_int "0") in
              _0_225 <> _0_224 in
            if uu____229 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s])
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
let prim_types uu____354 = []
let prim_constructors: (Prims.string* Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* (Prims.int* fixity)* Prims.string)
      Prims.option
  =
  fun uu____382  ->
    match uu____382 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____404  ->
               match uu____404 with | (y,uu____411,uu____412) -> x = y)
            infix_prim_ops
        else None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let _0_226 = as_bin_op p in _0_226 <> None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) Prims.option
  =
  fun uu____442  ->
    match uu____442 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____455  -> match uu____455 with | (y,uu____459) -> x = y)
            prim_uni_ops
        else None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let _0_227 = as_uni_op p in _0_227 <> None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol* Prims.string) Prims.option
  =
  fun uu____479  ->
    match uu____479 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____492  -> match uu____492 with | (y,uu____496) -> x = y)
            prim_constructors
        else None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let _0_228 = as_standard_constructor p in _0_228 <> None
let maybe_paren:
  ((Prims.int* fixity)* assoc) ->
    (Prims.int* fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____520  ->
    fun inner  ->
      fun doc  ->
        match uu____520 with
        | (outer,side) ->
            let noparens _inner _outer side =
              let uu____553 = _inner in
              match uu____553 with
              | (pi,fi) ->
                  let uu____558 = _outer in
                  (match uu____558 with
                   | (po,fo) ->
                       (pi > po) ||
                         ((match (fi, side) with
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
                           | (uu____563,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____564,uu____565) -> false))) in
            if noparens inner outer side
            then doc
            else FStar_Format.parens doc
let escape_byte_hex: FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let escape_char_hex: FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___113_581  ->
      match uu___113_581 with
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
        let _0_230 =
          let _0_229 = escape_or escape_char_hex c in Prims.strcat _0_229 "'" in
        Prims.strcat "'" _0_230
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
        let _0_232 =
          let _0_231 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat _0_231 "\"" in
        Prims.strcat "\"" _0_232
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let _0_234 =
          let _0_233 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat _0_233 "\"" in
        Prims.strcat "\"" _0_234
    | uu____635 ->
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
            FStar_Format.text
              (let _0_235 = FStar_Extraction_ML_Syntax.idsym x in
               FStar_All.pipe_left escape_tyvar _0_235)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc =
              FStar_Format.parens
                (FStar_Format.hbox
                   (FStar_Format.combine (FStar_Format.text " * ") doc)) in
            doc
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____672 ->
                  let args =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  FStar_Format.parens
                    (FStar_Format.hbox
                       (FStar_Format.combine (FStar_Format.text ", ") args)) in
            let name = ptsym currentModule name in
            FStar_Format.hbox
              (FStar_Format.reduce1 [args; FStar_Format.text name])
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____680,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let _0_236 =
              FStar_Format.hbox
                (FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]) in
            maybe_paren outer t_prio_fun _0_236
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____688 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____688
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
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e,t,t') ->
            let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
            let uu____740 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____740
            then
              FStar_Format.parens
                (FStar_Format.reduce
                   [FStar_Format.text "Prims.checked_cast"; doc])
            else
              FStar_Format.parens
                (FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc])
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs in
            FStar_Format.parens (FStar_Format.reduce docs)
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            FStar_Format.text (string_of_mlconstant c)
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____753) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            FStar_Format.text (ptsym currentModule path)
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____770 =
              match uu____770 with
              | (name,e) ->
                  let doc =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  FStar_Format.reduce1
                    (let _0_237 =
                       FStar_Format.text (ptsym currentModule (path, name)) in
                     [_0_237; FStar_Format.text "="; doc]) in
            FStar_Format.cbrackets
              (let _0_238 = FStar_List.map for1 fields in
               FStar_Format.combine (FStar_Format.text "; ") _0_238)
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____784 = is_standard_constructor ctor in
              if uu____784
              then
                Prims.snd (FStar_Option.get (as_standard_constructor ctor))
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____793 = is_standard_constructor ctor in
              if uu____793
              then
                Prims.snd (FStar_Option.get (as_standard_constructor ctor))
              else ptctor currentModule ctor in
            let args =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc =
              match (name, args) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____806,uu____807) ->
                  FStar_Format.reduce1
                    (let _0_240 =
                       let _0_239 =
                         FStar_Format.parens
                           (FStar_Format.combine (FStar_Format.text ", ")
                              args) in
                       [_0_239] in
                     (FStar_Format.text name) :: _0_240) in
            maybe_paren outer e_app_prio doc
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   FStar_Format.parens
                     (doc_of_expr currentModule (min_op_prec, NonAssoc) x))
                es in
            let docs =
              FStar_Format.parens
                (FStar_Format.combine (FStar_Format.text ", ") docs) in
            docs
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____819,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                FStar_Format.reduce
                  (let _0_242 =
                     let _0_241 = doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                     [_0_241] in
                   FStar_Format.hardline :: _0_242)
              else FStar_Format.empty in
            let doc = doc_of_lets currentModule (rec_, false, lets) in
            let body = doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            FStar_Format.parens
              (let _0_246 =
                 let _0_245 =
                   let _0_244 =
                     let _0_243 =
                       FStar_Format.reduce1 [FStar_Format.text "in"; body] in
                     [_0_243] in
                   doc :: _0_244 in
                 pre :: _0_245 in
               FStar_Format.combine FStar_Format.hardline _0_246)
        | FStar_Extraction_ML_Syntax.MLE_App (e,args) ->
            (match ((e.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____841::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____843;
                    FStar_Extraction_ML_Syntax.loc = uu____844;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____846)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____848;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____849;_}::[])
                 when
                 let _0_247 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 _0_247 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____879;
                            FStar_Extraction_ML_Syntax.loc = uu____880;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____882;
                       FStar_Extraction_ML_Syntax.loc = uu____883;_} when
                       let _0_249 = FStar_Extraction_ML_Syntax.idsym arg in
                       let _0_248 = FStar_Extraction_ML_Syntax.idsym arg' in
                       _0_249 = _0_248 -> branches
                   | e -> [(FStar_Extraction_ML_Syntax.MLP_Wild, None, e)] in
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
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e1::e2::[]) when
                 is_bin_op p -> doc_of_binop currentModule p e1 e2
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____914;
                   FStar_Extraction_ML_Syntax.loc = uu____915;_},unitVal::[]),e1::e2::[])
                 when
                 (is_bin_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_binop currentModule p e1 e2
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e1::[]) when
                 is_uni_op p -> doc_of_uniop currentModule p e1
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____925;
                   FStar_Extraction_ML_Syntax.loc = uu____926;_},unitVal::[]),e1::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e1
             | uu____931 ->
                 let e = doc_of_expr currentModule (e_app_prio, ILeft) e in
                 let args =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 FStar_Format.parens (FStar_Format.reduce1 (e :: args)))
        | FStar_Extraction_ML_Syntax.MLE_Proj (e,f) ->
            let e = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
            let doc =
              let uu____948 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____948
              then
                FStar_Format.reduce
                  [e; FStar_Format.text "."; FStar_Format.text (Prims.snd f)]
              else
                FStar_Format.reduce
                  (let _0_252 =
                     let _0_251 =
                       let _0_250 = FStar_Format.text (ptsym currentModule f) in
                       [_0_250] in
                     (FStar_Format.text ".") :: _0_251 in
                   e :: _0_252) in
            doc
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____968 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____968
              then
                FStar_Format.reduce1
                  (let _0_257 =
                     let _0_256 =
                       let _0_255 =
                         match xt with
                         | Some xxt ->
                             FStar_Format.reduce1
                               (let _0_254 =
                                  let _0_253 =
                                    doc_of_mltype currentModule outer xxt in
                                  [_0_253] in
                                (FStar_Format.text " : ") :: _0_254)
                         | uu____970 -> FStar_Format.text "" in
                       [_0_255; FStar_Format.text ")"] in
                     (FStar_Format.text x) :: _0_256 in
                   (FStar_Format.text "(") :: _0_257)
              else FStar_Format.text x in
            let ids =
              FStar_List.map
                (fun uu____979  ->
                   match uu____979 with
                   | ((x,uu____985),xt) -> bvar_annot x (Some xt)) ids in
            let body = doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc =
              FStar_Format.reduce1
                (let _0_259 =
                   let _0_258 = FStar_Format.reduce1 ids in
                   [_0_258; FStar_Format.text "->"; body] in
                 (FStar_Format.text "fun") :: _0_259) in
            FStar_Format.parens doc
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond = doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc =
              let _0_263 =
                let _0_262 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let _0_261 =
                  let _0_260 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [_0_260; FStar_Format.text "end"] in
                _0_262 :: _0_261 in
              FStar_Format.combine FStar_Format.hardline _0_263 in
            maybe_paren outer e_bin_prio_if doc
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond = doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc =
              let _0_271 =
                let _0_270 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let _0_269 =
                  let _0_268 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let _0_267 =
                    let _0_266 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let _0_265 =
                      let _0_264 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [_0_264; FStar_Format.text "end"] in
                    _0_266 :: _0_265 in
                  _0_268 :: _0_267 in
                _0_270 :: _0_269 in
              FStar_Format.combine FStar_Format.hardline _0_271 in
            maybe_paren outer e_bin_prio_if doc
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond = doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats = FStar_List.map (doc_of_branch currentModule) pats in
            let doc =
              let _0_272 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond;
                  FStar_Format.text "with"] in
              _0_272 :: pats in
            let doc = FStar_Format.combine FStar_Format.hardline doc in
            FStar_Format.parens doc
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            FStar_Format.reduce1
              (let _0_274 =
                 let _0_273 = FStar_Format.text (ptctor currentModule exn) in
                 [_0_273] in
               (FStar_Format.text "raise") :: _0_274)
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            FStar_Format.reduce1
              (let _0_278 =
                 let _0_277 = FStar_Format.text (ptctor currentModule exn) in
                 let _0_276 =
                   let _0_275 =
                     FStar_Format.parens
                       (FStar_Format.combine (FStar_Format.text ", ") args) in
                   [_0_275] in
                 _0_277 :: _0_276 in
               (FStar_Format.text "raise") :: _0_278)
        | FStar_Extraction_ML_Syntax.MLE_Try (e,pats) ->
            let _0_285 =
              let _0_284 =
                let _0_283 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let _0_282 =
                  let _0_281 =
                    let _0_280 =
                      let _0_279 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline _0_279 in
                    [_0_280] in
                  (FStar_Format.text "with") :: _0_281 in
                _0_283 :: _0_282 in
              (FStar_Format.text "try") :: _0_284 in
            FStar_Format.combine FStar_Format.hardline _0_285
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
          let uu____1062 = FStar_Option.get (as_bin_op p) in
          match uu____1062 with
          | (uu____1073,prio,txt) ->
              let e1 = doc_of_expr currentModule (prio, Left) e1 in
              let e2 = doc_of_expr currentModule (prio, Right) e2 in
              let doc = FStar_Format.reduce1 [e1; FStar_Format.text txt; e2] in
              FStar_Format.parens doc
and doc_of_uniop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____1090 = FStar_Option.get (as_uni_op p) in
        match uu____1090 with
        | (uu____1095,txt) ->
            let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e1] in
            FStar_Format.parens doc
and doc_of_pattern:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          FStar_Format.text (string_of_mlconstant c)
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (Prims.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1120 =
            match uu____1120 with
            | (name,p) ->
                FStar_Format.reduce1
                  (let _0_289 =
                     FStar_Format.text (ptsym currentModule (path, name)) in
                   let _0_288 =
                     let _0_287 =
                       let _0_286 = doc_of_pattern currentModule p in
                       [_0_286] in
                     (FStar_Format.text "=") :: _0_287 in
                   _0_289 :: _0_288) in
          FStar_Format.cbrackets
            (let _0_290 = FStar_List.map for1 fields in
             FStar_Format.combine (FStar_Format.text "; ") _0_290)
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1131 = is_standard_constructor ctor in
            if uu____1131
            then Prims.snd (FStar_Option.get (as_standard_constructor ctor))
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1140 = is_standard_constructor ctor in
            if uu____1140
            then Prims.snd (FStar_Option.get (as_standard_constructor ctor))
            else ptctor currentModule ctor in
          let doc =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                FStar_Format.reduce
                  (let _0_294 =
                     FStar_Format.parens (doc_of_pattern currentModule x) in
                   let _0_293 =
                     let _0_292 =
                       let _0_291 = doc_of_pattern currentModule xs in
                       [_0_291] in
                     (FStar_Format.text "::") :: _0_292 in
                   _0_294 :: _0_293)
            | (uu____1149,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1150)::[]) ->
                FStar_Format.reduce1
                  (let _0_297 =
                     let _0_296 =
                       let _0_295 = FStar_List.hd pats in
                       doc_of_pattern currentModule _0_295 in
                     [_0_296] in
                   (FStar_Format.text name) :: _0_297)
            | uu____1153 ->
                FStar_Format.reduce1
                  (let _0_300 =
                     let _0_299 =
                       FStar_Format.parens
                         (let _0_298 =
                            FStar_List.map (doc_of_pattern currentModule)
                              pats in
                          FStar_Format.combine (FStar_Format.text ", ")
                            _0_298) in
                     [_0_299] in
                   (FStar_Format.text name) :: _0_300) in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps = FStar_List.map (doc_of_pattern currentModule) ps in
          FStar_Format.parens
            (FStar_Format.combine (FStar_Format.text ", ") ps)
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps = FStar_List.map FStar_Format.parens ps in
          FStar_Format.combine (FStar_Format.text " | ") ps
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1170  ->
      match uu____1170 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                FStar_Format.reduce1
                  (let _0_302 =
                     let _0_301 = doc_of_pattern currentModule p in [_0_301] in
                   (FStar_Format.text "|") :: _0_302)
            | Some c ->
                let c = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                FStar_Format.reduce1
                  (let _0_304 =
                     let _0_303 = doc_of_pattern currentModule p in
                     [_0_303; FStar_Format.text "when"; c] in
                   (FStar_Format.text "|") :: _0_304) in
          let _0_308 =
            let _0_307 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let _0_306 =
              let _0_305 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [_0_305; FStar_Format.text "end"] in
            _0_307 :: _0_306 in
          FStar_Format.combine FStar_Format.hardline _0_308
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor* Prims.bool*
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1184  ->
      match uu____1184 with
      | (rec_,top_level,lets) ->
          let for1 uu____1197 =
            match uu____1197 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1200;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ids =
                  FStar_List.map
                    (fun uu____1217  ->
                       match uu____1217 with
                       | (x,uu____1221) -> FStar_Format.text x) ids in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1224 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1224
                     then
                       match tys with
                       | Some (_::_,_)|None  -> FStar_Format.text ""
                       | Some ([],ty) ->
                           let ty =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty]
                     else
                       if top_level
                       then
                         (match tys with
                          | None |Some (_::_,_) -> FStar_Format.text ""
                          | Some ([],ty) ->
                              let ty =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty])
                       else FStar_Format.text "") in
                FStar_Format.reduce1
                  (let _0_311 =
                     FStar_Format.text
                       (FStar_Extraction_ML_Syntax.idsym name) in
                   let _0_310 =
                     let _0_309 = FStar_Format.reduce1 ids in
                     [_0_309; ty_annot; FStar_Format.text "="; e] in
                   _0_311 :: _0_310) in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then
              FStar_Format.reduce1
                [FStar_Format.text "let"; FStar_Format.text "rec"]
            else FStar_Format.text "let" in
          let lets = FStar_List.map for1 lets in
          let lets =
            FStar_List.mapi
              (fun i  ->
                 fun doc  ->
                   FStar_Format.reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else FStar_Format.text "and";
                     doc]) lets in
          FStar_Format.combine FStar_Format.hardline lets
and doc_of_loc: FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____1266  ->
    match uu____1266 with
    | (lineno,file) ->
        let uu____1269 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1269
        then FStar_Format.empty
        else
          (let file = FStar_Util.basename file in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))])
let doc_of_mltydecl:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____1289 =
        match uu____1289 with
        | (uu____1298,x,mangle_opt,tparams,body) ->
            let x = match mangle_opt with | None  -> x | Some y -> y in
            let tparams =
              match tparams with
              | [] -> FStar_Format.empty
              | x::[] ->
                  FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x)
              | uu____1313 ->
                  let doc =
                    FStar_List.map
                      (fun x  ->
                         FStar_Format.text
                           (FStar_Extraction_ML_Syntax.idsym x)) tparams in
                  FStar_Format.parens
                    (FStar_Format.combine (FStar_Format.text ", ") doc) in
            let forbody body =
              match body with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1334 =
                    match uu____1334 with
                    | (name,ty) ->
                        let name = FStar_Format.text name in
                        let ty =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name; FStar_Format.text ":"; ty] in
                  FStar_Format.cbrackets
                    (let _0_312 = FStar_List.map forfield fields in
                     FStar_Format.combine (FStar_Format.text "; ") _0_312)
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1356 =
                    match uu____1356 with
                    | (name,tys) ->
                        (match tys with
                         | [] -> FStar_Format.text name
                         | uu____1364 ->
                             let tys =
                               FStar_List.map
                                 (doc_of_mltype currentModule
                                    (t_prio_tpl, Left)) tys in
                             let tys =
                               FStar_Format.combine (FStar_Format.text " * ")
                                 tys in
                             FStar_Format.reduce1
                               [FStar_Format.text name;
                               FStar_Format.text "of";
                               tys]) in
                  let ctors = FStar_List.map forctor ctors in
                  let ctors =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors in
                  FStar_Format.combine FStar_Format.hardline ctors in
            let doc =
              FStar_Format.reduce1
                (let _0_314 =
                   let _0_313 =
                     FStar_Format.text (ptsym currentModule ([], x)) in
                   [_0_313] in
                 tparams :: _0_314) in
            (match body with
             | None  -> doc
             | Some body ->
                 let body = forbody body in
                 let _0_316 =
                   let _0_315 =
                     FStar_Format.reduce1 [doc; FStar_Format.text "="] in
                   [_0_315; body] in
                 FStar_Format.combine FStar_Format.hardline _0_316) in
      let doc = FStar_List.map for1 decls in
      let doc =
        if (FStar_List.length doc) > (Prims.parse_int "0")
        then
          FStar_Format.reduce1
            (let _0_318 =
               let _0_317 =
                 FStar_Format.combine (FStar_Format.text " \n and ") doc in
               [_0_317] in
             (FStar_Format.text "type") :: _0_318)
        else FStar_Format.text "" in
      doc
let rec doc_of_sig1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let _0_324 =
            let _0_323 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let _0_322 =
              let _0_321 = doc_of_sig currentModule subsig in
              let _0_320 =
                let _0_319 = FStar_Format.reduce1 [FStar_Format.text "end"] in
                [_0_319] in
              _0_321 :: _0_320 in
            _0_323 :: _0_322 in
          FStar_Format.combine FStar_Format.hardline _0_324
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args =
            FStar_Format.parens
              (FStar_Format.combine (FStar_Format.text " * ") args) in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1424,ty)) ->
          let ty = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and doc_of_sig:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs in
      FStar_Format.reduce docs
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
          let args =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args =
            FStar_Format.parens
              (FStar_Format.combine (FStar_Format.text " * ") args) in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1458,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          FStar_Format.reduce1
            (let _0_328 =
               let _0_327 =
                 let _0_326 =
                   let _0_325 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                   [_0_325] in
                 (FStar_Format.text "=") :: _0_326 in
               (FStar_Format.text "_") :: _0_327 in
             (FStar_Format.text "let") :: _0_328)
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let doc_of_mod:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc = doc_of_mod1 currentModule x in
             [doc;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1479 ->
                  FStar_Format.empty
              | uu____1480 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string* FStar_Format.doc) Prims.list
  =
  fun uu____1486  ->
    match uu____1486 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1524 =
          match uu____1524 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub) ->
              let x = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"] in
              let tail = FStar_Format.reduce1 [FStar_Format.text "end"] in
              let doc =
                FStar_Option.map
                  (fun uu____1563  ->
                     match uu____1563 with | (s,uu____1567) -> doc_of_sig x s)
                  sigmod in
              let sub = FStar_List.map for1_sig sub in
              let sub =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline]) sub in
              FStar_Format.reduce
                (let _0_331 =
                   let _0_330 =
                     let _0_329 = FStar_Format.reduce sub in
                     [_0_329; FStar_Format.cat tail FStar_Format.hardline] in
                   (match doc with
                    | None  -> FStar_Format.empty
                    | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                     _0_330 in
                 (FStar_Format.cat head FStar_Format.hardline) :: _0_331)
        and for1_mod istop uu____1584 =
          match uu____1584 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub) ->
              let x = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head =
                FStar_Format.reduce1
                  (let uu____1618 =
                     FStar_Extraction_ML_Util.codegen_fsharp () in
                   if uu____1618
                   then [FStar_Format.text "module"; FStar_Format.text x]
                   else
                     if Prims.op_Negation istop
                     then
                       [FStar_Format.text "module";
                       FStar_Format.text x;
                       FStar_Format.text "=";
                       FStar_Format.text "struct"]
                     else []) in
              let tail =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc =
                FStar_Option.map
                  (fun uu____1629  ->
                     match uu____1629 with | (uu____1632,m) -> doc_of_mod x m)
                  sigmod in
              let sub = FStar_List.map (for1_mod false) sub in
              let sub =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline]) sub in
              let prefix =
                let uu____1650 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____1650
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let _0_339 =
                let _0_338 =
                  let _0_337 =
                    let _0_336 =
                      let _0_335 =
                        let _0_334 =
                          let _0_333 =
                            let _0_332 = FStar_Format.reduce sub in
                            [_0_332;
                            FStar_Format.cat tail FStar_Format.hardline] in
                          (match doc with
                           | None  -> FStar_Format.empty
                           | Some s ->
                               FStar_Format.cat s FStar_Format.hardline)
                            :: _0_333 in
                        FStar_Format.hardline :: _0_334 in
                      (FStar_Format.text "open Prims") :: _0_335 in
                    FStar_Format.hardline :: _0_336 in
                  head :: _0_337 in
                FStar_List.append prefix _0_338 in
              FStar_All.pipe_left FStar_Format.reduce _0_339 in
        let docs =
          FStar_List.map
            (fun uu____1670  ->
               match uu____1670 with
               | (x,s,m) ->
                   let _0_341 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let _0_340 = for1_mod true (x, s, m) in (_0_341, _0_340))
            mllib in
        docs
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
      let doc =
        let _0_342 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr _0_342 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc =
        let _0_343 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype _0_343 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc