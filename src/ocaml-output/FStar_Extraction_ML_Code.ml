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
    match projectee with | Prefix  -> true | uu____27 -> false
  
let uu___is_Postfix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____31 -> false
  
let uu___is_Infix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____36 -> false
  
let __proj__Infix__item___0 : fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0 
type opprec = (Prims.int * fixity)
type level = (opprec * assoc)
let t_prio_fun : (Prims.int * fixity) =
  ((Prims.parse_int "10"), (Infix Right)) 
let t_prio_tpl : (Prims.int * fixity) =
  ((Prims.parse_int "20"), (Infix NonAssoc)) 
let t_prio_name : (Prims.int * fixity) = ((Prims.parse_int "30"), Postfix) 
let e_bin_prio_lambda : (Prims.int * fixity) =
  ((Prims.parse_int "5"), Prefix) 
let e_bin_prio_if : (Prims.int * fixity) = ((Prims.parse_int "15"), Prefix) 
let e_bin_prio_letin : (Prims.int * fixity) =
  ((Prims.parse_int "19"), Prefix) 
let e_bin_prio_or : (Prims.int * fixity) =
  ((Prims.parse_int "20"), (Infix Left)) 
let e_bin_prio_and : (Prims.int * fixity) =
  ((Prims.parse_int "25"), (Infix Left)) 
let e_bin_prio_eq : (Prims.int * fixity) =
  ((Prims.parse_int "27"), (Infix NonAssoc)) 
let e_bin_prio_order : (Prims.int * fixity) =
  ((Prims.parse_int "29"), (Infix NonAssoc)) 
let e_bin_prio_op1 : (Prims.int * fixity) =
  ((Prims.parse_int "30"), (Infix Left)) 
let e_bin_prio_op2 : (Prims.int * fixity) =
  ((Prims.parse_int "40"), (Infix Left)) 
let e_bin_prio_op3 : (Prims.int * fixity) =
  ((Prims.parse_int "50"), (Infix Left)) 
let e_bin_prio_op4 : (Prims.int * fixity) =
  ((Prims.parse_int "60"), (Infix Left)) 
let e_bin_prio_comb : (Prims.int * fixity) =
  ((Prims.parse_int "70"), (Infix Left)) 
let e_bin_prio_seq : (Prims.int * fixity) =
  ((Prims.parse_int "100"), (Infix Left)) 
let e_app_prio : (Prims.int * fixity) =
  ((Prims.parse_int "10000"), (Infix Left)) 
let min_op_prec : (Prims.int * fixity) =
  ((~- (Prims.parse_int "1")), (Infix NonAssoc)) 
let max_op_prec : (Prims.int * fixity) =
  (FStar_Util.max_int, (Infix NonAssoc)) 
let rec in_ns x =
  match x with
  | ([],uu____101) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____115,uu____116) -> false 
let path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun currentModule  ->
    fun ns  ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns  in
      match ns' = currentModule with
      | true  -> []
      | uu____132 ->
          let cg_libs = FStar_Options.codegen_libs ()  in
          let ns_len = FStar_List.length ns  in
          let found =
            FStar_Util.find_map cg_libs
              (fun cg_path  ->
                 let cg_len = FStar_List.length cg_path  in
                 match (FStar_List.length cg_path) < ns_len with
                 | true  ->
                     let uu____154 = FStar_Util.first_N cg_len ns  in
                     (match uu____154 with
                      | (pfx,sfx) ->
                          (match pfx = cg_path with
                           | true  ->
                               Some
                                 (let _0_210 =
                                    let _0_209 =
                                      FStar_Extraction_ML_Util.flatten_ns sfx
                                       in
                                    [_0_209]  in
                                  FStar_List.append pfx _0_210)
                           | uu____173 -> None))
                 | uu____175 -> None)
             in
          (match found with | None  -> [ns'] | Some x -> x)
  
let mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____188 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____188 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____191 ->
          let uu____192 = x  in
          (match uu____192 with
           | (ns,x) ->
               let _0_211 = path_of_ns currentModule ns  in (_0_211, x))
  
let ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____201 =
      let _0_213 =
        FStar_Char.lowercase (FStar_String.get s (Prims.parse_int "0"))  in
      let _0_212 = FStar_String.get s (Prims.parse_int "0")  in
      _0_213 <> _0_212  in
    match uu____201 with | true  -> Prims.strcat "l__" s | uu____202 -> s
  
let ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      match FStar_List.isEmpty (Prims.fst mlp) with
      | true  -> ptsym_of_symbol (Prims.snd mlp)
      | uu____211 ->
          let uu____212 = mlpath_of_mlpath currentModule mlp  in
          (match uu____212 with
           | (p,s) ->
               let _0_216 =
                 let _0_215 = let _0_214 = ptsym_of_symbol s  in [_0_214]  in
                 FStar_List.append p _0_215  in
               FStar_String.concat "." _0_216)
  
let ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____223 = mlpath_of_mlpath currentModule mlp  in
      match uu____223 with
      | (p,s) ->
          let s =
            let uu____229 =
              let _0_218 =
                FStar_Char.uppercase
                  (FStar_String.get s (Prims.parse_int "0"))
                 in
              let _0_217 = FStar_String.get s (Prims.parse_int "0")  in
              _0_218 <> _0_217  in
            match uu____229 with
            | true  -> Prims.strcat "U__" s
            | uu____230 -> s  in
          FStar_String.concat "." (FStar_List.append p [s])
  
let infix_prim_ops :
  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list =
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
let prim_uni_ops : (Prims.string * Prims.string) Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")] 
let prim_types uu____354 = [] 
let prim_constructors : (Prims.string * Prims.string) Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")] 
let is_prims_ns :
  FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool =
  fun ns  -> ns = ["Prims"] 
let as_bin_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) *
      Prims.string) Prims.option
  =
  fun uu____400  ->
    match uu____400 with
    | (ns,x) ->
        (match is_prims_ns ns with
         | true  ->
             FStar_List.tryFind
               (fun uu____404  ->
                  match uu____404 with | (y,uu____411,uu____412) -> x = y)
               infix_prim_ops
         | uu____417 -> None)
  
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let _0_219 = as_bin_op p  in _0_219 <> None 
let as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option
  =
  fun uu____467  ->
    match uu____467 with
    | (ns,x) ->
        (match is_prims_ns ns with
         | true  ->
             FStar_List.tryFind
               (fun uu____455  ->
                  match uu____455 with | (y,uu____459) -> x = y) prim_uni_ops
         | uu____460 -> None)
  
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> let _0_220 = as_uni_op p  in _0_220 <> None 
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false 
let as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option
  =
  fun uu____508  ->
    match uu____508 with
    | (ns,x) ->
        (match is_prims_ns ns with
         | true  ->
             FStar_List.tryFind
               (fun uu____492  ->
                  match uu____492 with | (y,uu____496) -> x = y)
               prim_constructors
         | uu____497 -> None)
  
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  = fun p  -> let _0_221 = as_standard_constructor p  in _0_221 <> None 
let maybe_paren :
  ((Prims.int * fixity) * assoc) ->
    (Prims.int * fixity) -> FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____553  ->
    fun inner  ->
      fun doc1  ->
        match uu____553 with
        | (outer,side) ->
            let noparens _inner _outer side =
              let uu____553 = _inner  in
              match uu____553 with
              | (pi,fi) ->
                  let uu____558 = _outer  in
                  (match uu____558 with
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
                           | (uu____563,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____564,uu____565) -> false)))
               in
            (match noparens inner outer side with
             | true  -> doc
             | uu____566 -> FStar_Format.parens doc)
  
let escape_byte_hex : FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let escape_char_hex : FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let escape_or :
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___116_614  ->
      match uu___116_614 with
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
        let _0_223 =
          let _0_222 = escape_or escape_char_hex c  in
          Prims.strcat _0_222 "'"  in
        Prims.strcat "'" _0_223
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
        let _0_225 =
          let _0_224 = FStar_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat _0_224 "\""  in
        Prims.strcat "\"" _0_225
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let _0_227 =
          let _0_226 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat _0_226 "\""  in
        Prims.strcat "\"" _0_227
    | uu____635 ->
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
              match FStar_Util.starts_with s "'_" with
              | true  -> FStar_Util.replace_char s '_' 'u'
              | uu____656 -> s  in
            FStar_Format.text
              (let _0_228 = FStar_Extraction_ML_Syntax.idsym x  in
               FStar_All.pipe_left escape_tyvar _0_228)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc =
              FStar_Format.parens
                (FStar_Format.hbox
                   (FStar_Format.combine (FStar_Format.text " * ") doc))
               in
            doc
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____715 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  FStar_Format.parens
                    (FStar_Format.hbox
                       (FStar_Format.combine (FStar_Format.text ", ") args))
               in
            let name = ptsym currentModule name  in
            FStar_Format.hbox
              (FStar_Format.reduce1 [args; FStar_Format.text name])
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____680,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let _0_229 =
              FStar_Format.hbox
                (FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2])
               in
            maybe_paren outer t_prio_fun _0_229
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____688 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            (match uu____688 with
             | true  -> FStar_Format.text "obj"
             | uu____689 -> FStar_Format.text "Obj.t")

and doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        doc_of_mltype' currentModule outer
          (FStar_Extraction_ML_Util.resugar_mlty ty)

let rec doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e,t,t') ->
            let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
            let uu____740 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            (match uu____740 with
             | true  ->
                 FStar_Format.parens
                   (FStar_Format.reduce
                      [FStar_Format.text "Prims.checked_cast"; doc])
             | uu____741 ->
                 FStar_Format.parens
                   (FStar_Format.reduce
                      [FStar_Format.text "Obj.magic ";
                      FStar_Format.parens doc]))
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es
               in
            let docs =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs
               in
            FStar_Format.parens (FStar_Format.reduce docs)
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____803 = string_of_mlconstant c in
            FStar_Format.text uu____803
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____805) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____807 = ptsym currentModule path in
            FStar_Format.text uu____807
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____770 =
              match uu____770 with
              | (name,e) ->
                  let doc =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  FStar_Format.reduce1
                    (let _0_230 =
                       FStar_Format.text (ptsym currentModule (path, name))
                        in
                     [_0_230; FStar_Format.text "="; doc])
               in
            FStar_Format.cbrackets
              (let _0_231 = FStar_List.map for1 fields  in
               FStar_Format.combine (FStar_Format.text "; ") _0_231)
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____784 = is_standard_constructor ctor  in
              match uu____784 with
              | true  ->
                  Prims.snd (FStar_Option.get (as_standard_constructor ctor))
              | uu____787 -> ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____793 = is_standard_constructor ctor  in
              match uu____793 with
              | true  ->
                  Prims.snd (FStar_Option.get (as_standard_constructor ctor))
              | uu____796 -> ptctor currentModule ctor  in
            let args =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let doc =
              match (name, args) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____806,uu____807) ->
                  FStar_Format.reduce1
                    (let _0_233 =
                       let _0_232 =
                         FStar_Format.parens
                           (FStar_Format.combine (FStar_Format.text ", ")
                              args)
                          in
                       [_0_232]  in
                     (FStar_Format.text name) :: _0_233)
               in
            maybe_paren outer e_app_prio doc
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   FStar_Format.parens
                     (doc_of_expr currentModule (min_op_prec, NonAssoc) x))
                es
               in
            let docs =
              FStar_Format.parens
                (FStar_Format.combine (FStar_Format.text ", ") docs)
               in
            docs
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____819,lets),body) ->
            let pre =
              match e.FStar_Extraction_ML_Syntax.loc <>
                      FStar_Extraction_ML_Syntax.dummy_loc
              with
              | true  ->
                  FStar_Format.reduce
                    (let _0_235 =
                       let _0_234 =
                         doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                       [_0_234]  in
                     FStar_Format.hardline :: _0_235)
              | uu____829 -> FStar_Format.empty  in
            let doc = doc_of_lets currentModule (rec_, false, lets)  in
            let body = doc_of_expr currentModule (min_op_prec, NonAssoc) body
               in
            FStar_Format.parens
              (let _0_239 =
                 let _0_238 =
                   let _0_237 =
                     let _0_236 =
                       FStar_Format.reduce1 [FStar_Format.text "in"; body]
                        in
                     [_0_236]  in
                   doc :: _0_237  in
                 pre :: _0_238  in
               FStar_Format.combine FStar_Format.hardline _0_239)
        | FStar_Extraction_ML_Syntax.MLE_App (e,args) ->
            (match ((e.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____936::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____938;
                    FStar_Extraction_ML_Syntax.loc = uu____939;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____941)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____943;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____944;_}::[])
                 when
                 let _0_240 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                    in
                 _0_240 = "FStar.All.try_with" ->
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
                       let _0_242 = FStar_Extraction_ML_Syntax.idsym arg  in
                       let _0_241 = FStar_Extraction_ML_Syntax.idsym arg'  in
                       _0_242 = _0_241 -> branches
                   | e -> [(FStar_Extraction_ML_Syntax.MLP_Wild, None, e)]
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1012;
                   FStar_Extraction_ML_Syntax.loc = uu____1013;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1023;
                   FStar_Extraction_ML_Syntax.loc = uu____1024;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e1
             | uu____931 ->
                 let e = doc_of_expr currentModule (e_app_prio, ILeft) e  in
                 let args =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 FStar_Format.parens (FStar_Format.reduce1 (e :: args)))
        | FStar_Extraction_ML_Syntax.MLE_Proj (e,f) ->
            let e = doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
            let doc =
              let uu____948 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              match uu____948 with
              | true  ->
                  FStar_Format.reduce
                    [e;
                    FStar_Format.text ".";
                    FStar_Format.text (Prims.snd f)]
              | uu____950 ->
                  FStar_Format.reduce
                    (let _0_245 =
                       let _0_244 =
                         let _0_243 =
                           FStar_Format.text (ptsym currentModule f)  in
                         [_0_243]  in
                       (FStar_Format.text ".") :: _0_244  in
                     e :: _0_245)
               in
            doc
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____968 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              match uu____968 with
              | true  ->
                  FStar_Format.reduce1
                    (let _0_250 =
                       let _0_249 =
                         let _0_248 =
                           match xt with
                           | Some xxt ->
                               FStar_Format.reduce1
                                 (let _0_247 =
                                    let _0_246 =
                                      doc_of_mltype currentModule outer xxt
                                       in
                                    [_0_246]  in
                                  (FStar_Format.text " : ") :: _0_247)
                           | uu____970 -> FStar_Format.text ""  in
                         [_0_248; FStar_Format.text ")"]  in
                       (FStar_Format.text x) :: _0_249  in
                     (FStar_Format.text "(") :: _0_250)
              | uu____972 -> FStar_Format.text x  in
            let ids =
              FStar_List.map
                (fun uu____979  ->
                   match uu____979 with
                   | ((x,uu____985),xt) -> bvar_annot x (Some xt)) ids
               in
            let body = doc_of_expr currentModule (min_op_prec, NonAssoc) body
               in
            let doc =
              FStar_Format.reduce1
                (let _0_252 =
                   let _0_251 = FStar_Format.reduce1 ids  in
                   [_0_251; FStar_Format.text "->"; body]  in
                 (FStar_Format.text "fun") :: _0_252)
               in
            FStar_Format.parens doc
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,None ) ->
            let cond = doc_of_expr currentModule (min_op_prec, NonAssoc) cond
               in
            let doc =
              let _0_256 =
                let _0_255 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let _0_254 =
                  let _0_253 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [_0_253; FStar_Format.text "end"]  in
                _0_255 :: _0_254  in
              FStar_Format.combine FStar_Format.hardline _0_256  in
            maybe_paren outer e_bin_prio_if doc
        | FStar_Extraction_ML_Syntax.MLE_If (cond,e1,Some e2) ->
            let cond = doc_of_expr currentModule (min_op_prec, NonAssoc) cond
               in
            let doc =
              let _0_264 =
                let _0_263 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let _0_262 =
                  let _0_261 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let _0_260 =
                    let _0_259 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let _0_258 =
                      let _0_257 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [_0_257; FStar_Format.text "end"]  in
                    _0_259 :: _0_258  in
                  _0_261 :: _0_260  in
                _0_263 :: _0_262  in
              FStar_Format.combine FStar_Format.hardline _0_264  in
            maybe_paren outer e_bin_prio_if doc
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond = doc_of_expr currentModule (min_op_prec, NonAssoc) cond
               in
            let pats = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc =
              let _0_265 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond;
                  FStar_Format.text "with"]
                 in
              _0_265 :: pats  in
            let doc = FStar_Format.combine FStar_Format.hardline doc  in
            FStar_Format.parens doc
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            FStar_Format.reduce1
              (let _0_267 =
                 let _0_266 = FStar_Format.text (ptctor currentModule exn)
                    in
                 [_0_266]  in
               (FStar_Format.text "raise") :: _0_267)
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            FStar_Format.reduce1
              (let _0_271 =
                 let _0_270 = FStar_Format.text (ptctor currentModule exn)
                    in
                 let _0_269 =
                   let _0_268 =
                     FStar_Format.parens
                       (FStar_Format.combine (FStar_Format.text ", ") args)
                      in
                   [_0_268]  in
                 _0_270 :: _0_269  in
               (FStar_Format.text "raise") :: _0_271)
        | FStar_Extraction_ML_Syntax.MLE_Try (e,pats) ->
            let _0_278 =
              let _0_277 =
                let _0_276 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                let _0_275 =
                  let _0_274 =
                    let _0_273 =
                      let _0_272 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline _0_272  in
                    [_0_273]  in
                  (FStar_Format.text "with") :: _0_274  in
                _0_276 :: _0_275  in
              (FStar_Format.text "try") :: _0_277  in
            FStar_Format.combine FStar_Format.hardline _0_278

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
          let uu____1062 = FStar_Option.get (as_bin_op p)  in
          match uu____1062 with
          | (uu____1073,prio,txt) ->
              let e1 = doc_of_expr currentModule (prio, Left) e1  in
              let e2 = doc_of_expr currentModule (prio, Right) e2  in
              let doc = FStar_Format.reduce1 [e1; FStar_Format.text txt; e2]
                 in
              FStar_Format.parens doc

and doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____1090 = FStar_Option.get (as_uni_op p)  in
        match uu____1090 with
        | (uu____1095,txt) ->
            let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e1]
               in
            FStar_Format.parens doc

and doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____1286 = string_of_mlconstant c in
          FStar_Format.text uu____1286
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (Prims.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1303 =
            match uu____1303 with
            | (name,p) ->
                FStar_Format.reduce1
                  (let _0_282 =
                     FStar_Format.text (ptsym currentModule (path, name))  in
                   let _0_281 =
                     let _0_280 =
                       let _0_279 = doc_of_pattern currentModule p  in
                       [_0_279]  in
                     (FStar_Format.text "=") :: _0_280  in
                   _0_282 :: _0_281)
             in
          FStar_Format.cbrackets
            (let _0_283 = FStar_List.map for1 fields  in
             FStar_Format.combine (FStar_Format.text "; ") _0_283)
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1131 = is_standard_constructor ctor  in
            match uu____1131 with
            | true  ->
                Prims.snd (FStar_Option.get (as_standard_constructor ctor))
            | uu____1134 -> ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1140 = is_standard_constructor ctor  in
            match uu____1140 with
            | true  ->
                Prims.snd (FStar_Option.get (as_standard_constructor ctor))
            | uu____1143 -> ptctor currentModule ctor  in
          let doc =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                FStar_Format.reduce
                  (let _0_287 =
                     FStar_Format.parens (doc_of_pattern currentModule x)  in
                   let _0_286 =
                     let _0_285 =
                       let _0_284 = doc_of_pattern currentModule xs  in
                       [_0_284]  in
                     (FStar_Format.text "::") :: _0_285  in
                   _0_287 :: _0_286)
            | (uu____1149,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1150)::[]) ->
                FStar_Format.reduce1
                  (let _0_290 =
                     let _0_289 =
                       let _0_288 = FStar_List.hd pats  in
                       doc_of_pattern currentModule _0_288  in
                     [_0_289]  in
                   (FStar_Format.text name) :: _0_290)
            | uu____1153 ->
                FStar_Format.reduce1
                  (let _0_293 =
                     let _0_292 =
                       FStar_Format.parens
                         (let _0_291 =
                            FStar_List.map (doc_of_pattern currentModule)
                              pats
                             in
                          FStar_Format.combine (FStar_Format.text ", ")
                            _0_291)
                        in
                     [_0_292]  in
                   (FStar_Format.text name) :: _0_293)
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps = FStar_List.map (doc_of_pattern currentModule) ps  in
          FStar_Format.parens
            (FStar_Format.combine (FStar_Format.text ", ") ps)
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps = FStar_List.map FStar_Format.parens ps  in
          FStar_Format.combine (FStar_Format.text " | ") ps

and doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1403  ->
      match uu____1403 with
      | (p,cond,e) ->
          let case =
            match cond with
            | None  ->
                FStar_Format.reduce1
                  (let _0_295 =
                     let _0_294 = doc_of_pattern currentModule p  in [_0_294]
                      in
                   (FStar_Format.text "|") :: _0_295)
            | Some c ->
                let c = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                FStar_Format.reduce1
                  (let _0_297 =
                     let _0_296 = doc_of_pattern currentModule p  in
                     [_0_296; FStar_Format.text "when"; c]  in
                   (FStar_Format.text "|") :: _0_297)
             in
          let _0_301 =
            let _0_300 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let _0_299 =
              let _0_298 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [_0_298; FStar_Format.text "end"]  in
            _0_300 :: _0_299  in
          FStar_Format.combine FStar_Format.hardline _0_301

and doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool *
      FStar_Extraction_ML_Syntax.mllb Prims.list) -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1433  ->
      match uu____1433 with
      | (rec_,top_level,lets) ->
          let for1 uu____1446 =
            match uu____1446 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1449;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ids =
                  FStar_List.map
                    (fun uu____1217  ->
                       match uu____1217 with
                       | (x,uu____1221) -> FStar_Format.text x) ids
                   in
                let ty_annot =
                  match Prims.op_Negation pt with
                  | true  -> FStar_Format.text ""
                  | uu____1223 ->
                      let uu____1224 =
                        (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                          ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                             top_level)
                         in
                      (match uu____1224 with
                       | true  ->
                           (match tys with
                            | Some (_::_,_)|None  -> FStar_Format.text ""
                            | Some ([],ty) ->
                                let ty =
                                  doc_of_mltype currentModule
                                    (min_op_prec, NonAssoc) ty
                                   in
                                FStar_Format.reduce1
                                  [FStar_Format.text ":"; ty])
                       | uu____1240 ->
                           (match top_level with
                            | true  ->
                                (match tys with
                                 | None |Some (_::_,_) ->
                                     FStar_Format.text ""
                                 | Some ([],ty) ->
                                     let ty =
                                       doc_of_mltype currentModule
                                         (min_op_prec, NonAssoc) ty
                                        in
                                     FStar_Format.reduce1
                                       [FStar_Format.text ":"; ty])
                            | uu____1256 -> FStar_Format.text ""))
                   in
                FStar_Format.reduce1
                  (let _0_304 =
                     FStar_Format.text
                       (FStar_Extraction_ML_Syntax.idsym name)
                      in
                   let _0_303 =
                     let _0_302 = FStar_Format.reduce1 ids  in
                     [_0_302; ty_annot; FStar_Format.text "="; e]  in
                   _0_304 :: _0_303)
             in
          let letdoc =
            match rec_ = FStar_Extraction_ML_Syntax.Rec with
            | true  ->
                FStar_Format.reduce1
                  [FStar_Format.text "let"; FStar_Format.text "rec"]
            | uu____1258 -> FStar_Format.text "let"  in
          let lets = FStar_List.map for1 lets  in
          let lets =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   FStar_Format.reduce1
                     [(match i = (Prims.parse_int "0") with
                       | true  -> letdoc
                       | uu____1265 -> FStar_Format.text "and");
                     doc]) lets
             in
          FStar_Format.combine FStar_Format.hardline lets

and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____1266  ->
    match uu____1266 with
    | (lineno,file) ->
        let uu____1525 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ())
           in
        (match uu____1269 with
         | true  -> FStar_Format.empty
         | uu____1270 ->
             let file = FStar_Util.basename file  in
             FStar_Format.reduce1
               [FStar_Format.text "#";
               FStar_Format.num lineno;
               FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))])

let doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____1289 =
        match uu____1289 with
        | (uu____1298,x,mangle_opt,tparams,body) ->
            let x = match mangle_opt with | None  -> x | Some y -> y  in
            let tparams =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1569 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1569
              | uu____1570 ->
                  let doc1 =
                    FStar_List.map
                      (fun x  ->
                         FStar_Format.text
                           (FStar_Extraction_ML_Syntax.idsym x)) tparams
                     in
                  FStar_Format.parens
                    (FStar_Format.combine (FStar_Format.text ", ") doc)
               in
            let forbody body =
              match body with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1593 =
                    match uu____1593 with
                    | (name,ty) ->
                        let name = FStar_Format.text name  in
                        let ty =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name; FStar_Format.text ":"; ty]
                     in
                  FStar_Format.cbrackets
                    (let _0_305 = FStar_List.map forfield fields  in
                     FStar_Format.combine (FStar_Format.text "; ") _0_305)
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1618 =
                    match uu____1618 with
                    | (name,tys) ->
                        (match tys with
                         | [] -> FStar_Format.text name
                         | uu____1626 ->
                             let tys1 =
                               FStar_List.map
                                 (doc_of_mltype currentModule
                                    (t_prio_tpl, Left)) tys
                                in
                             let tys =
                               FStar_Format.combine (FStar_Format.text " * ")
                                 tys
                                in
                             FStar_Format.reduce1
                               [FStar_Format.text name;
                               FStar_Format.text "of";
                               tys])
                     in
                  let ctors = FStar_List.map forctor ctors  in
                  let ctors =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors
                     in
                  FStar_Format.combine FStar_Format.hardline ctors
               in
            let doc =
              FStar_Format.reduce1
                (let _0_307 =
                   let _0_306 =
                     FStar_Format.text (ptsym currentModule ([], x))  in
                   [_0_306]  in
                 tparams :: _0_307)
               in
            (match body with
             | None  -> doc
             | Some body ->
                 let body = forbody body  in
                 let _0_309 =
                   let _0_308 =
                     FStar_Format.reduce1 [doc; FStar_Format.text "="]  in
                   [_0_308; body]  in
                 FStar_Format.combine FStar_Format.hardline _0_309)
         in
      let doc = FStar_List.map for1 decls  in
      let doc =
        match (FStar_List.length doc) > (Prims.parse_int "0") with
        | true  ->
            FStar_Format.reduce1
              (let _0_311 =
                 let _0_310 =
                   FStar_Format.combine (FStar_Format.text " \n and ") doc
                    in
                 [_0_310]  in
               (FStar_Format.text "type") :: _0_311)
        | uu____1397 -> FStar_Format.text ""  in
      doc
  
let rec doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____1688 =
            let uu____1690 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let _0_315 =
              let _0_314 = doc_of_sig currentModule subsig  in
              let _0_313 =
                let _0_312 = FStar_Format.reduce1 [FStar_Format.text "end"]
                   in
                [_0_312]  in
              _0_314 :: _0_313  in
            _0_316 :: _0_315  in
          FStar_Format.combine FStar_Format.hardline _0_317
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args =
            FStar_Format.parens
              (FStar_Format.combine (FStar_Format.text " * ") args)
             in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1424,ty)) ->
          let ty = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty  in
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
      let docs = FStar_List.map (doc_of_sig1 currentModule) s  in
      let docs =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs
         in
      FStar_Format.reduce docs

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
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args =
            FStar_Format.parens
              (FStar_Format.combine (FStar_Format.text " * ") args)
             in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1745,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          FStar_Format.reduce1
            (let _0_321 =
               let _0_320 =
                 let _0_319 =
                   let _0_318 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                   [_0_318]  in
                 (FStar_Format.text "=") :: _0_319  in
               (FStar_Format.text "_") :: _0_320  in
             (FStar_Format.text "let") :: _0_321)
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
  
let doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc = doc_of_mod1 currentModule x  in
             [doc;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1775 ->
                  FStar_Format.empty
              | uu____1480 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs)
  
let rec doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list
  =
  fun uu____1782  ->
    match uu____1782 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1524 =
          match uu____1524 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub) ->
              let x = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x1;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"]
                 in
              let tail = FStar_Format.reduce1 [FStar_Format.text "end"]  in
              let doc =
                FStar_Option.map
                  (fun uu____1563  ->
                     match uu____1563 with | (s,uu____1567) -> doc_of_sig x s)
                  sigmod
                 in
              let sub = FStar_List.map for1_sig sub  in
              let sub =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline]) sub
                 in
              FStar_Format.reduce
                (let _0_324 =
                   let _0_323 =
                     let _0_322 = FStar_Format.reduce sub  in
                     [_0_322; FStar_Format.cat tail FStar_Format.hardline]
                      in
                   (match doc with
                    | None  -> FStar_Format.empty
                    | Some s -> FStar_Format.cat s FStar_Format.hardline) ::
                     _0_323
                    in
                 (FStar_Format.cat head FStar_Format.hardline) :: _0_324)
        
        and for1_mod istop uu____1584 =
          match uu____1584 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub) ->
              let x = FStar_Extraction_ML_Util.flatten_mlpath x  in
              let head =
                FStar_Format.reduce1
                  (let uu____1618 =
                     FStar_Extraction_ML_Util.codegen_fsharp ()  in
                   match uu____1618 with
                   | true  ->
                       [FStar_Format.text "module"; FStar_Format.text x]
                   | uu____1620 ->
                       (match Prims.op_Negation istop with
                        | true  ->
                            [FStar_Format.text "module";
                            FStar_Format.text x;
                            FStar_Format.text "=";
                            FStar_Format.text "struct"]
                        | uu____1622 -> []))
                 in
              let tail =
                match Prims.op_Negation istop with
                | true  -> FStar_Format.reduce1 [FStar_Format.text "end"]
                | uu____1624 -> FStar_Format.reduce1 []  in
              let doc =
                FStar_Option.map
                  (fun uu____1629  ->
                     match uu____1629 with | (uu____1632,m) -> doc_of_mod x m)
                  sigmod
                 in
              let sub = FStar_List.map (for1_mod false) sub  in
              let sub =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline]) sub
                 in
              let prefix =
                let uu____1650 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                match uu____1650 with
                | true  ->
                    [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                       FStar_Format.hardline]
                | uu____1652 -> []  in
              let _0_332 =
                let _0_331 =
                  let _0_330 =
                    let _0_329 =
                      let _0_328 =
                        let _0_327 =
                          let _0_326 =
                            let _0_325 = FStar_Format.reduce sub  in
                            [_0_325;
                            FStar_Format.cat tail FStar_Format.hardline]  in
                          (match doc with
                           | None  -> FStar_Format.empty
                           | Some s ->
                               FStar_Format.cat s FStar_Format.hardline)
                            :: _0_326
                           in
                        FStar_Format.hardline :: _0_327  in
                      (FStar_Format.text "open Prims") :: _0_328  in
                    FStar_Format.hardline :: _0_329  in
                  head :: _0_330  in
                FStar_List.append prefix _0_331  in
              FStar_All.pipe_left FStar_Format.reduce _0_332
         in
        let docs =
          FStar_List.map
            (fun uu____1990  ->
               match uu____1990 with
               | (x,s,m) ->
                   let _0_334 = FStar_Extraction_ML_Util.flatten_mlpath x  in
                   let _0_333 = for1_mod true (x, s, m)  in (_0_334, _0_333))
            mllib
           in
        docs
  
let doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string * FStar_Format.doc) Prims.list
  = fun mllib  -> doc_of_mllib_r mllib 
let string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc =
        let _0_335 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr _0_335 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc
  
let string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc =
        let _0_336 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype _0_336 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc
  