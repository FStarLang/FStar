open Prims
type assoc =
<<<<<<< HEAD
  | ILeft 
  | IRight 
  | Left 
  | Right 
  | NonAssoc 
let uu___is_ILeft : assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____5 -> false 
let uu___is_IRight : assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____10 -> false
  
let uu___is_Left : assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____15 -> false 
let uu___is_Right : assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____20 -> false 
let uu___is_NonAssoc : assoc -> Prims.bool =
=======
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
let (uu___is_ILeft :assoc -> Prims.bool)=
  fun projectee  -> match projectee with | ILeft  -> true | uu____5 -> false
let (uu___is_IRight :assoc -> Prims.bool)=
  fun projectee  ->
    match projectee with | IRight  -> true | uu____10 -> false
let (uu___is_Left :assoc -> Prims.bool)=
  fun projectee  -> match projectee with | Left  -> true | uu____15 -> false
let (uu___is_Right :assoc -> Prims.bool)=
  fun projectee  -> match projectee with | Right  -> true | uu____20 -> false
let (uu___is_NonAssoc :assoc -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____25 -> false
  
type fixity =
<<<<<<< HEAD
  | Prefix 
  | Postfix 
  | Infix of assoc 
let uu___is_Prefix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____34 -> false
  
let uu___is_Postfix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____39 -> false
  
let uu___is_Infix : fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____45 -> false
  
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
=======
  | Prefix
  | Postfix
  | Infix of assoc
let (uu___is_Prefix :fixity -> Prims.bool)=
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____34 -> false
let (uu___is_Postfix :fixity -> Prims.bool)=
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____39 -> false
let (uu___is_Infix :fixity -> Prims.bool)=
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____45 -> false
let (__proj__Infix__item___0 :fixity -> assoc)=
  fun projectee  -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
let (t_prio_fun :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "10"), (Infix Right))
let (t_prio_tpl :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "20"), (Infix NonAssoc))
let (t_prio_name :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "30"), Postfix)
let (e_bin_prio_lambda :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "5"), Prefix)
let (e_bin_prio_if :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "15"), Prefix)
let (e_bin_prio_letin :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "19"), Prefix)
let (e_bin_prio_or :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "20"), (Infix Left))
let (e_bin_prio_and :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "25"), (Infix Left))
let (e_bin_prio_eq :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "27"), (Infix NonAssoc))
let (e_bin_prio_order :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "29"), (Infix NonAssoc))
let (e_bin_prio_op1 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "30"), (Infix Left))
let (e_bin_prio_op2 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "40"), (Infix Left))
let (e_bin_prio_op3 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "50"), (Infix Left))
let (e_bin_prio_op4 :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "60"), (Infix Left))
let (e_bin_prio_comb :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "70"), (Infix Left))
let (e_bin_prio_seq :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "100"), (Infix Left))
let (e_app_prio :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((Prims.parse_int "10000"), (Infix Left))
let (min_op_prec :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let (max_op_prec :(Prims.int,fixity) FStar_Pervasives_Native.tuple2)=
  (FStar_Util.max_int, (Infix NonAssoc))
>>>>>>> taramana_pointers_with_codes_modifies
let rec in_ns :
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool=
  fun x  ->
    match x with
    | ([],uu____163) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____186,uu____187) -> false
<<<<<<< HEAD
  
let path_of_ns :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
=======
let (path_of_ns
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     Prims.string Prims.list -> Prims.string Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
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
                  let uu____247 = FStar_Util.first_N cg_len ns  in
                  match uu____247 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____280 =
                           let uu____283 =
                             let uu____286 =
                               FStar_Extraction_ML_Util.flatten_ns sfx  in
                             [uu____286]  in
                           FStar_List.append pfx uu____283  in
                         FStar_Pervasives_Native.Some uu____280
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None)
            in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
<<<<<<< HEAD
  
let mlpath_of_mlpath :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
=======
let (mlpath_of_mlpath
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun x  ->
      let uu____312 = FStar_Extraction_ML_Syntax.string_of_mlpath x  in
      match uu____312 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____317 ->
          let uu____318 = x  in
          (match uu____318 with
           | (ns,x1) ->
<<<<<<< HEAD
               let uu____325 = path_of_ns currentModule ns  in
               (uu____325, x1))
  
let ptsym_of_symbol :
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
=======
               let uu____325 = path_of_ns currentModule ns in (uu____325, x1))
let (ptsym_of_symbol
  :FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun s  ->
    let uu____334 =
      let uu____335 =
        let uu____336 = FStar_String.get s (Prims.parse_int "0")  in
        FStar_Char.lowercase uu____336  in
      let uu____337 = FStar_String.get s (Prims.parse_int "0")  in
      uu____335 <> uu____337  in
    if uu____334 then Prims.strcat "l__" s else s
<<<<<<< HEAD
  
let ptsym :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
=======
let (ptsym
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____352 = mlpath_of_mlpath currentModule mlp  in
         match uu____352 with
         | (p,s) ->
             let uu____359 =
               let uu____362 =
                 let uu____365 = ptsym_of_symbol s  in [uu____365]  in
               FStar_List.append p uu____362  in
             FStar_String.concat "." uu____359)
<<<<<<< HEAD
  
let ptctor :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
=======
let (ptctor
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun mlp  ->
      let uu____374 = mlpath_of_mlpath currentModule mlp  in
      match uu____374 with
      | (p,s) ->
          let s1 =
            let uu____382 =
              let uu____383 =
                let uu____384 = FStar_String.get s (Prims.parse_int "0")  in
                FStar_Char.uppercase uu____384  in
              let uu____385 = FStar_String.get s (Prims.parse_int "0")  in
              uu____383 <> uu____385  in
            if uu____382 then Prims.strcat "U__" s else s  in
          FStar_String.concat "." (FStar_List.append p [s1])
<<<<<<< HEAD
  
let infix_prim_ops :
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list
  =
=======
let (infix_prim_ops
  :(Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
     FStar_Pervasives_Native.tuple3 Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  ("op_Modulus", e_bin_prio_order, "mod")] 
let prim_uni_ops :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")] 
let prim_types : 'Auu____629 . Prims.unit -> 'Auu____629 Prims.list =
  fun uu____632  -> [] 
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
=======
  ("op_Modulus", e_bin_prio_order, "mod")]
let (prim_uni_ops
  :(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)=
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")]
let prim_types : 'Auu____629 . Prims.unit -> 'Auu____629 Prims.list=
  fun uu____632  -> []
let (prim_constructors
  :(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)=
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let (is_prims_ns
  :FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool)=
  fun ns  -> ns = ["Prims"]
let (as_bin_op
  :FStar_Extraction_ML_Syntax.mlpath ->
     (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                            FStar_Pervasives_Native.tuple2,
       Prims.string) FStar_Pervasives_Native.tuple3
       FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu____684  ->
    match uu____684 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____729  ->
               match uu____729 with | (y,uu____741,uu____742) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
<<<<<<< HEAD
  
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____766 = as_bin_op p  in uu____766 <> FStar_Pervasives_Native.None
  
let as_uni_op :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
=======
let (is_bin_op :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  ->
    let uu____766 = as_bin_op p in uu____766 <> FStar_Pervasives_Native.None
let (as_uni_op
  :FStar_Extraction_ML_Syntax.mlpath ->
     (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu____810  ->
    match uu____810 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____836  -> match uu____836 with | (y,uu____842) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
<<<<<<< HEAD
  
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____852 = as_uni_op p  in uu____852 <> FStar_Pervasives_Native.None
  
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false 
let as_standard_constructor :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
=======
let (is_uni_op :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  ->
    let uu____852 = as_uni_op p in uu____852 <> FStar_Pervasives_Native.None
let (is_standard_type :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
  fun p  -> false
let (as_standard_constructor
  :FStar_Extraction_ML_Syntax.mlpath ->
     (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu____882  ->
    match uu____882 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____908  -> match uu____908 with | (y,uu____914) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
<<<<<<< HEAD
  
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
=======
let (is_standard_constructor
  :FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun p  ->
    let uu____924 = as_standard_constructor p  in
    uu____924 <> FStar_Pervasives_Native.None
<<<<<<< HEAD
  
let maybe_paren :
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
=======
let (maybe_paren
  :((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
     FStar_Pervasives_Native.tuple2 ->
     (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
       FStar_Format.doc -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu____962  ->
    fun inner  ->
      fun doc1  ->
        match uu____962 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1013 = _inner  in
              match uu____1013 with
              | (pi,fi) ->
                  let uu____1020 = _outer  in
                  (match uu____1020 with
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
                           | (uu____1027,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1028,uu____1029) -> false)))
               in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
<<<<<<< HEAD
  
let escape_byte_hex : FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x) 
let escape_char_hex : FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x) 
let escape_or :
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
=======
let (escape_byte_hex :FStar_BaseTypes.byte -> Prims.string)=
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let (escape_char_hex :FStar_BaseTypes.char -> Prims.string)=
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let (escape_or
  :(FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun fallback  ->
    fun uu___122_1049  ->
      match uu___122_1049 with
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
<<<<<<< HEAD
  
let string_of_mlconstant :
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
=======
let (string_of_mlconstant
  :FStar_Extraction_ML_Syntax.mlconstant -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let uu____1069 =
          let uu____1070 = escape_or escape_char_hex c  in
          Prims.strcat uu____1070 "'"  in
        Prims.strcat "'" uu____1069
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1094,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1106,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1132 =
          let uu____1133 = FStar_Bytes.f_encode escape_byte_hex bytes  in
          Prims.strcat uu____1133 "\""  in
        Prims.strcat "\"" uu____1132
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1135 =
          let uu____1136 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars
             in
          Prims.strcat uu____1136 "\""  in
        Prims.strcat "\"" uu____1135
    | uu____1137 ->
        failwith "TODO: extract integer constants properly into OCaml"
<<<<<<< HEAD
  
let rec doc_of_mltype' :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
=======
let rec (doc_of_mltype'
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s '_' 'u'
              else s  in
            let uu____1159 =
              let uu____1160 = FStar_Extraction_ML_Syntax.idsym x  in
              FStar_All.pipe_left escape_tyvar uu____1160  in
            FStar_Format.text uu____1159
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys
               in
            let doc2 =
              let uu____1172 =
                let uu____1173 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1  in
                FStar_Format.hbox uu____1173  in
              FStar_Format.parens uu____1172  in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1186 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args
                     in
                  let uu____1196 =
                    let uu____1197 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.hbox uu____1197  in
                  FStar_Format.parens uu____1196
               in
            let name1 = ptsym currentModule name  in
            let uu____1199 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1]  in
            FStar_Format.hbox uu____1199
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1201,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1  in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2  in
            let uu____1213 =
              let uu____1214 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2]  in
              FStar_Format.hbox uu____1214  in
            maybe_paren outer t_prio_fun uu____1213
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1215 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1215
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
<<<<<<< HEAD

and doc_of_mltype :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
=======
and (doc_of_mltype
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1220 = FStar_Extraction_ML_Util.resugar_mlty ty  in
        doc_of_mltype' currentModule outer uu____1220
<<<<<<< HEAD

let rec doc_of_expr :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
=======
let rec (doc_of_expr
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let uu____1274 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
            if uu____1274
            then
              let uu____1275 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1]
                 in
              FStar_Format.parens uu____1275
            else
              (let uu____1277 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1]
                  in
               FStar_Format.parens uu____1277)
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
            let uu____1293 = FStar_Format.reduce docs2  in
            FStar_Format.parens uu____1293
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1295 = string_of_mlconstant c  in
            FStar_Format.text uu____1295
        | FStar_Extraction_ML_Syntax.MLE_Var (x,uu____1297) ->
            FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1299 = ptsym currentModule path  in
            FStar_Format.text uu____1299
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1325 =
              match uu____1325 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1337 =
                    let uu____1340 =
                      let uu____1341 = ptsym currentModule (path, name)  in
                      FStar_Format.text uu____1341  in
                    [uu____1340; FStar_Format.text "="; doc1]  in
                  FStar_Format.reduce1 uu____1337
               in
            let uu____1344 =
              let uu____1345 = FStar_List.map for1 fields  in
              FStar_Format.combine (FStar_Format.text "; ") uu____1345  in
            FStar_Format.cbrackets uu____1344
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1356 = is_standard_constructor ctor  in
              if uu____1356
              then
                let uu____1357 =
                  let uu____1362 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1362  in
                FStar_Pervasives_Native.snd uu____1357
              else ptctor currentModule ctor  in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1381 = is_standard_constructor ctor  in
              if uu____1381
              then
                let uu____1382 =
                  let uu____1387 = as_standard_constructor ctor  in
                  FStar_Option.get uu____1387  in
                FStar_Pervasives_Native.snd uu____1382
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
              | (uu____1413,uu____1414) ->
                  let uu____1419 =
                    let uu____1422 =
                      let uu____1425 =
                        let uu____1426 =
                          FStar_Format.combine (FStar_Format.text ", ") args1
                           in
                        FStar_Format.parens uu____1426  in
                      [uu____1425]  in
                    (FStar_Format.text name) :: uu____1422  in
                  FStar_Format.reduce1 uu____1419
               in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____1436 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x  in
                   FStar_Format.parens uu____1436) es
               in
            let docs2 =
              let uu____1442 =
                FStar_Format.combine (FStar_Format.text ", ") docs1  in
              FStar_Format.parens uu____1442  in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1444,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1460 =
                  let uu____1463 =
                    let uu____1466 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc  in
                    [uu____1466]  in
                  FStar_Format.hardline :: uu____1463  in
                FStar_Format.reduce uu____1460
              else FStar_Format.empty  in
            let doc1 = doc_of_lets currentModule (rec_, false, lets)  in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let uu____1476 =
              let uu____1477 =
                let uu____1480 =
                  let uu____1483 =
                    let uu____1486 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1]
                       in
                    [uu____1486]  in
                  doc1 :: uu____1483  in
                pre :: uu____1480  in
              FStar_Format.combine FStar_Format.hardline uu____1477  in
            FStar_Format.parens uu____1476
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1496::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1498;
                    FStar_Extraction_ML_Syntax.loc = uu____1499;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1501)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1503;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1504;_}::[])
                 when
                 let uu____1539 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____1539 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1562;
                            FStar_Extraction_ML_Syntax.loc = uu____1563;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1565;
                       FStar_Extraction_ML_Syntax.loc = uu____1566;_} when
                       let uu____1587 = FStar_Extraction_ML_Syntax.idsym arg
                          in
                       let uu____1588 = FStar_Extraction_ML_Syntax.idsym arg'
                          in
                       uu____1587 = uu____1588 -> branches
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1624;
                   FStar_Extraction_ML_Syntax.loc = uu____1625;_},unitVal::[]),e11::e2::[])
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
                   FStar_Extraction_ML_Syntax.mlty = uu____1638;
                   FStar_Extraction_ML_Syntax.loc = uu____1639;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1646 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1
                    in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args
                    in
                 let uu____1665 = FStar_Format.reduce1 (e2 :: args1)  in
                 FStar_Format.parens uu____1665)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
            let doc1 =
              let uu____1674 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1674
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1678 =
                   let uu____1681 =
                     let uu____1684 =
                       let uu____1687 =
                         let uu____1688 = ptsym currentModule f  in
                         FStar_Format.text uu____1688  in
                       [uu____1687]  in
                     (FStar_Format.text ".") :: uu____1684  in
                   e2 :: uu____1681  in
                 FStar_Format.reduce uu____1678)
               in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1714 = FStar_Extraction_ML_Util.codegen_fsharp ()  in
              if uu____1714
              then
                let uu____1715 =
                  let uu____1718 =
                    let uu____1721 =
                      let uu____1724 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1726 =
                              let uu____1729 =
                                let uu____1732 =
                                  doc_of_mltype currentModule outer xxt  in
                                [uu____1732]  in
                              (FStar_Format.text " : ") :: uu____1729  in
                            FStar_Format.reduce1 uu____1726
                        | uu____1733 -> FStar_Format.text ""  in
                      [uu____1724; FStar_Format.text ")"]  in
                    (FStar_Format.text x) :: uu____1721  in
                  (FStar_Format.text "(") :: uu____1718  in
                FStar_Format.reduce1 uu____1715
              else FStar_Format.text x  in
            let ids1 =
              FStar_List.map
                (fun uu____1752  ->
                   match uu____1752 with
                   | ((x,uu____1762),xt) ->
                       bvar_annot x (FStar_Pervasives_Native.Some xt)) ids
               in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body  in
            let doc1 =
              let uu____1774 =
                let uu____1777 =
                  let uu____1780 = FStar_Format.reduce1 ids1  in
                  [uu____1780; FStar_Format.text "->"; body1]  in
                (FStar_Format.text "fun") :: uu____1777  in
              FStar_Format.reduce1 uu____1774  in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1791 =
                let uu____1794 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1795 =
                  let uu____1798 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  [uu____1798; FStar_Format.text "end"]  in
                uu____1794 :: uu____1795  in
              FStar_Format.combine FStar_Format.hardline uu____1791  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let doc1 =
              let uu____1814 =
                let uu____1817 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"]
                   in
                let uu____1818 =
                  let uu____1821 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                  let uu____1826 =
                    let uu____1829 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"]
                       in
                    let uu____1830 =
                      let uu____1833 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2
                         in
                      [uu____1833; FStar_Format.text "end"]  in
                    uu____1829 :: uu____1830  in
                  uu____1821 :: uu____1826  in
                uu____1817 :: uu____1818  in
              FStar_Format.combine FStar_Format.hardline uu____1814  in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond  in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats  in
            let doc1 =
              let uu____1871 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"]
                 in
              uu____1871 :: pats1  in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1  in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1876 =
              let uu____1879 =
                let uu____1882 =
                  let uu____1883 = ptctor currentModule exn  in
                  FStar_Format.text uu____1883  in
                [uu____1882]  in
              (FStar_Format.text "raise") :: uu____1879  in
            FStar_Format.reduce1 uu____1876
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args
               in
            let uu____1897 =
              let uu____1900 =
                let uu____1903 =
                  let uu____1904 = ptctor currentModule exn  in
                  FStar_Format.text uu____1904  in
                let uu____1905 =
                  let uu____1908 =
                    let uu____1909 =
                      FStar_Format.combine (FStar_Format.text ", ") args1  in
                    FStar_Format.parens uu____1909  in
                  [uu____1908]  in
                uu____1903 :: uu____1905  in
              (FStar_Format.text "raise") :: uu____1900  in
            FStar_Format.reduce1 uu____1897
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1932 =
              let uu____1935 =
                let uu____1938 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1  in
                let uu____1943 =
                  let uu____1946 =
                    let uu____1949 =
                      let uu____1950 =
                        FStar_List.map (doc_of_branch currentModule) pats  in
                      FStar_Format.combine FStar_Format.hardline uu____1950
                       in
                    [uu____1949]  in
                  (FStar_Format.text "with") :: uu____1946  in
                uu____1938 :: uu____1943  in
              (FStar_Format.text "try") :: uu____1935  in
            FStar_Format.combine FStar_Format.hardline uu____1932
<<<<<<< HEAD
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1

and doc_of_binop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
=======
and (doc_of_binop
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath ->
       FStar_Extraction_ML_Syntax.mlexpr ->
         FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____1963 =
            let uu____1974 = as_bin_op p  in FStar_Option.get uu____1974  in
          match uu____1963 with
          | (uu____1997,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1  in
              let e21 = doc_of_expr currentModule (prio, Right) e2  in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21]  in
              FStar_Format.parens doc1
<<<<<<< HEAD

and doc_of_uniop :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
=======
and (doc_of_uniop
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpath ->
       FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____2022 =
          let uu____2027 = as_uni_op p  in FStar_Option.get uu____2027  in
        match uu____2022 with
        | (uu____2038,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1
               in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11]
               in
            FStar_Format.parens doc1
<<<<<<< HEAD

and doc_of_pattern :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
=======
and (doc_of_pattern
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____2049 = string_of_mlconstant c  in
          FStar_Format.text uu____2049
      | FStar_Extraction_ML_Syntax.MLP_Var x ->
          FStar_Format.text (FStar_Pervasives_Native.fst x)
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2076 =
            match uu____2076 with
            | (name,p) ->
                let uu____2083 =
                  let uu____2086 =
                    let uu____2087 = ptsym currentModule (path, name)  in
                    FStar_Format.text uu____2087  in
                  let uu____2090 =
                    let uu____2093 =
                      let uu____2096 = doc_of_pattern currentModule p  in
                      [uu____2096]  in
                    (FStar_Format.text "=") :: uu____2093  in
                  uu____2086 :: uu____2090  in
                FStar_Format.reduce1 uu____2083
             in
          let uu____2097 =
            let uu____2098 = FStar_List.map for1 fields  in
            FStar_Format.combine (FStar_Format.text "; ") uu____2098  in
          FStar_Format.cbrackets uu____2097
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2109 = is_standard_constructor ctor  in
            if uu____2109
            then
              let uu____2110 =
                let uu____2115 = as_standard_constructor ctor  in
                FStar_Option.get uu____2115  in
              FStar_Pervasives_Native.snd uu____2110
            else ptctor currentModule ctor  in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2134 = is_standard_constructor ctor  in
            if uu____2134
            then
              let uu____2135 =
                let uu____2140 = as_standard_constructor ctor  in
                FStar_Option.get uu____2140  in
              FStar_Pervasives_Native.snd uu____2135
            else ptctor currentModule ctor  in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2159 =
                  let uu____2162 =
                    let uu____2163 = doc_of_pattern currentModule x  in
                    FStar_Format.parens uu____2163  in
                  let uu____2164 =
                    let uu____2167 =
                      let uu____2170 = doc_of_pattern currentModule xs  in
                      [uu____2170]  in
                    (FStar_Format.text "::") :: uu____2167  in
                  uu____2162 :: uu____2164  in
                FStar_Format.reduce uu____2159
            | (uu____2171,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2172)::[]) ->
                let uu____2177 =
                  let uu____2180 =
                    let uu____2183 =
                      let uu____2184 = FStar_List.hd pats  in
                      doc_of_pattern currentModule uu____2184  in
                    [uu____2183]  in
                  (FStar_Format.text name) :: uu____2180  in
                FStar_Format.reduce1 uu____2177
            | uu____2185 ->
                let uu____2192 =
                  let uu____2195 =
                    let uu____2198 =
                      let uu____2199 =
                        let uu____2200 =
                          FStar_List.map (doc_of_pattern currentModule) pats
                           in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2200
                         in
                      FStar_Format.parens uu____2199  in
                    [uu____2198]  in
                  (FStar_Format.text name) :: uu____2195  in
                FStar_Format.reduce1 uu____2192
             in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let uu____2213 = FStar_Format.combine (FStar_Format.text ", ") ps1
             in
          FStar_Format.parens uu____2213
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps  in
          let ps2 = FStar_List.map FStar_Format.parens ps1  in
          FStar_Format.combine (FStar_Format.text " | ") ps2
<<<<<<< HEAD

and doc_of_branch :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
=======
and (doc_of_branch
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun uu____2224  ->
      match uu____2224 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2233 =
                  let uu____2236 =
                    let uu____2239 = doc_of_pattern currentModule p  in
                    [uu____2239]  in
                  (FStar_Format.text "|") :: uu____2236  in
                FStar_Format.reduce1 uu____2233
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c
                   in
                let uu____2246 =
                  let uu____2249 =
                    let uu____2252 = doc_of_pattern currentModule p  in
                    [uu____2252; FStar_Format.text "when"; c1]  in
                  (FStar_Format.text "|") :: uu____2249  in
                FStar_Format.reduce1 uu____2246
             in
          let uu____2253 =
            let uu____2256 =
              FStar_Format.reduce1
<<<<<<< HEAD
                [case; FStar_Format.text "->"; FStar_Format.text "begin"]
               in
            let uu____2257 =
              let uu____2260 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
              [uu____2260; FStar_Format.text "end"]  in
            uu____2256 :: uu____2257  in
          FStar_Format.combine FStar_Format.hardline uu____2253

and doc_of_lets :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
=======
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2251 =
              let uu____2254 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2254; FStar_Format.text "end"] in
            uu____2250 :: uu____2251 in
          FStar_Format.combine FStar_Format.hardline uu____2247
and (doc_of_lets
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                          Prims.list)
       FStar_Pervasives_Native.tuple3 -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun uu____2266  ->
      match uu____2266 with
      | (rec_,top_level,lets) ->
          let for1 uu____2285 =
            match uu____2285 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2288;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e
                   in
                let ids = []  in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2303 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level)
                        in
                     if uu____2303
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2304::uu____2305,uu____2306) ->
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
                                let uu____2358 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x)))
                                   in
                                FStar_All.pipe_right uu____2358
                                  FStar_Format.reduce1
                                 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "")
                   in
                let uu____2372 =
                  let uu____2375 =
                    let uu____2376 = FStar_Extraction_ML_Syntax.idsym name
                       in
                    FStar_Format.text uu____2376  in
                  let uu____2377 =
                    let uu____2380 = FStar_Format.reduce1 ids  in
                    [uu____2380; ty_annot; FStar_Format.text "="; e1]  in
                  uu____2375 :: uu____2377  in
                FStar_Format.reduce1 uu____2372
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
<<<<<<< HEAD

and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____2394  ->
    match uu____2394 with
=======
and (doc_of_loc :FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc)=
  fun uu____2388  ->
    match uu____2388 with
>>>>>>> taramana_pointers_with_codes_modifies
    | (lineno,file) ->
        let uu____2397 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ())
           in
        if uu____2397
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file  in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])
<<<<<<< HEAD

let doc_of_mltydecl :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
=======
let (doc_of_mltydecl
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun decls  ->
      let for1 uu____2429 =
        match uu____2429 with
        | (uu____2448,x,mangle_opt,tparams,uu____2452,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y  in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____2470 = FStar_Extraction_ML_Syntax.idsym x2  in
                  FStar_Format.text uu____2470
              | uu____2471 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____2480 = FStar_Extraction_ML_Syntax.idsym x2
                            in
                         FStar_Format.text uu____2480) tparams
                     in
                  let uu____2481 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1  in
                  FStar_Format.parens uu____2481
               in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2505 =
                    match uu____2505 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name  in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty
                           in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1]
                     in
                  let uu____2518 =
                    let uu____2519 = FStar_List.map forfield fields  in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2519
                     in
                  FStar_Format.cbrackets uu____2518
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2552 =
                    match uu____2552 with
                    | (name,tys) ->
                        let uu____2577 = FStar_List.split tys  in
                        (match uu____2577 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2596 ->
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
              let uu____2626 =
                let uu____2629 =
                  let uu____2632 =
                    let uu____2633 = ptsym currentModule ([], x1)  in
                    FStar_Format.text uu____2633  in
                  [uu____2632]  in
                tparams1 :: uu____2629  in
              FStar_Format.reduce1 uu____2626  in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1  in
                 let uu____2638 =
                   let uu____2641 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="]  in
                   [uu____2641; body2]  in
                 FStar_Format.combine FStar_Format.hardline uu____2638)
         in
      let doc1 = FStar_List.map for1 decls  in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2664 =
            let uu____2667 =
              let uu____2670 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1  in
              [uu____2670]  in
            (FStar_Format.text "type") :: uu____2667  in
          FStar_Format.reduce1 uu____2664
        else FStar_Format.text ""  in
      doc2
<<<<<<< HEAD
  
let rec doc_of_sig1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
=======
let rec (doc_of_sig1
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____2688 =
            let uu____2691 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="]
               in
            let uu____2692 =
              let uu____2695 = doc_of_sig currentModule subsig  in
              let uu____2696 =
                let uu____2699 =
                  FStar_Format.reduce1 [FStar_Format.text "end"]  in
                [uu____2699]  in
              uu____2695 :: uu____2696  in
            uu____2691 :: uu____2692  in
          FStar_Format.combine FStar_Format.hardline uu____2688
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args
             in
          let args2 =
            let uu____2717 =
              FStar_Format.combine (FStar_Format.text " * ") args1  in
            FStar_Format.parens uu____2717  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2719,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
             in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
<<<<<<< HEAD

and doc_of_sig :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
=======
and (doc_of_sig
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD

let doc_of_mod1 :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc
  =
=======
let (doc_of_mod1
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
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
            let uu____2789 =
              FStar_Format.combine (FStar_Format.text " * ") args2  in
            FStar_Format.parens uu____2789  in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____2792,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____2801 =
            let uu____2804 =
              let uu____2807 =
                let uu____2810 =
                  let uu____2813 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e  in
                  [uu____2813]  in
                (FStar_Format.text "=") :: uu____2810  in
              (FStar_Format.text "_") :: uu____2807  in
            (FStar_Format.text "let") :: uu____2804  in
          FStar_Format.reduce1 uu____2801
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
<<<<<<< HEAD
  
let doc_of_mod :
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
=======
let (doc_of_mod
  :FStar_Extraction_ML_Syntax.mlsymbol ->
     FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun currentModule  ->
    fun m  ->
      let docs1 =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x  in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2839 ->
                  FStar_Format.empty
              | uu____2840 -> FStar_Format.hardline);
             FStar_Format.hardline]) m
         in
      FStar_Format.reduce (FStar_List.flatten docs1)
<<<<<<< HEAD
  
let rec doc_of_mllib_r :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2850  ->
    match uu____2850 with
=======
let rec (doc_of_mllib_r
  :FStar_Extraction_ML_Syntax.mllib ->
     (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2
       Prims.list)=
  fun uu____2844  ->
    match uu____2844 with
>>>>>>> taramana_pointers_with_codes_modifies
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2916 =
          match uu____2916 with
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
                  (fun uu____2989  ->
                     match uu____2989 with
                     | (s,uu____2995) -> doc_of_sig x1 s) sigmod
                 in
              let sub2 = FStar_List.map for1_sig sub1  in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2
                 in
              let uu____3022 =
                let uu____3025 =
                  let uu____3028 =
                    let uu____3031 = FStar_Format.reduce sub3  in
                    [uu____3031;
                    FStar_Format.cat tail1 FStar_Format.hardline]  in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3028
                   in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3025
                 in
              FStar_Format.reduce uu____3022
        
        and for1_mod istop uu____3034 =
          match uu____3034 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name  in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3102 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives")
                       in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)]
                 in
              let head1 =
                let uu____3113 =
                  let uu____3116 = FStar_Extraction_ML_Util.codegen_fsharp ()
                     in
                  if uu____3116
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
                FStar_Format.reduce1 uu____3113  in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 []  in
              let doc1 =
                FStar_Option.map
                  (fun uu____3135  ->
                     match uu____3135 with
                     | (uu____3140,m) -> doc_of_mod target_mod_name m) sigmod
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
                let uu____3171 = FStar_Extraction_ML_Util.codegen_fsharp ()
                   in
                if uu____3171
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else []  in
              let uu____3175 =
                let uu____3178 =
                  let uu____3181 =
                    let uu____3184 =
                      let uu____3187 =
                        let uu____3190 =
                          let uu____3193 = FStar_Format.reduce sub3  in
                          [uu____3193;
                          FStar_Format.cat tail1 FStar_Format.hardline]  in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3190
                         in
                      FStar_Format.hardline :: uu____3187  in
                    FStar_List.append maybe_open_pervasives uu____3184  in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3181
                   in
                FStar_List.append prefix1 uu____3178  in
              FStar_All.pipe_left FStar_Format.reduce uu____3175
         in
        let docs1 =
          FStar_List.map
            (fun uu____3232  ->
               match uu____3232 with
               | (x,s,m) ->
                   let uu____3282 = FStar_Extraction_ML_Util.flatten_mlpath x
                      in
                   let uu____3283 = for1_mod true (x, s, m)  in
                   (uu____3282, uu____3283)) mllib
           in
        docs1
<<<<<<< HEAD
  
let doc_of_mllib :
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib 
let string_of_mlexpr :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
=======
let (doc_of_mllib
  :FStar_Extraction_ML_Syntax.mllib ->
     (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2
       Prims.list)=
  fun mllib  -> doc_of_mllib_r mllib
let (string_of_mlexpr
  :FStar_Extraction_ML_Syntax.mlpath ->
     FStar_Extraction_ML_Syntax.mlexpr -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3315 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_expr uu____3315 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
<<<<<<< HEAD
  
let string_of_mlty :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
=======
let (string_of_mlty
  :FStar_Extraction_ML_Syntax.mlpath ->
     FStar_Extraction_ML_Syntax.mlty -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3329 = FStar_Extraction_ML_Util.flatten_mlpath cmod  in
        doc_of_mltype uu____3329 (min_op_prec, NonAssoc) e  in
      FStar_Format.pretty (Prims.parse_int "0") doc1
  