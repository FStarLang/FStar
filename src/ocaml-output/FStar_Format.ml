open Prims
type doc =
  | Doc of Prims.string 
let (uu___is_Doc : doc -> Prims.bool) = fun projectee  -> true 
let (__proj__Doc__item___0 : doc -> Prims.string) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
let (empty : doc) = Doc "" 
let (hardline : doc) = Doc "\n" 
let (text : Prims.string -> doc) = fun s  -> Doc s 
let (num : Prims.int -> doc) = fun i  -> Doc (Prims.string_of_int i) 
let (break_ : Prims.int -> doc) = fun i  -> Doc "" 
let (break0 : doc) = break_ (Prims.parse_int "0") 
let (break1 : doc) = text " " 
let (enclose : doc -> doc -> doc -> doc) =
  fun uu____44  ->
    fun uu____45  ->
      fun uu____46  ->
        match (uu____44, uu____45, uu____46) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.strcat l (Prims.strcat x r))
  
let (brackets : doc -> doc) =
  fun uu____54  ->
    match uu____54 with | Doc d -> enclose (text "[") (text "]") (Doc d)
  
let (cbrackets : doc -> doc) =
  fun uu____60  ->
    match uu____60 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____66  ->
    match uu____66 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____76  ->
    fun uu____77  ->
      match (uu____76, uu____77) with
      | (Doc d1,Doc d2) -> Doc (Prims.strcat d1 d2)
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (group : doc -> doc) =
  fun uu____93  -> match uu____93 with | Doc d -> Doc d 
let (groups : doc Prims.list -> doc) =
  fun docs  -> let uu____104 = reduce docs  in group uu____104 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____115  ->
    fun docs  ->
      match uu____115 with
      | Doc sep ->
          let select uu____127 =
            match uu____127 with
            | Doc d ->
                if d = ""
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some d
             in
          let docs1 = FStar_List.choose select docs  in
          Doc (FStar_String.concat sep docs1)
  
let (cat1 : doc -> doc -> doc) =
  fun d1  -> fun d2  -> reduce [d1; break1; d2] 
let (reduce1 : doc Prims.list -> doc) = fun docs  -> combine break1 docs 
let (nest : Prims.int -> doc -> doc) =
  fun i  -> fun uu____165  -> match uu____165 with | Doc d -> Doc d 
let (align : doc Prims.list -> doc) =
  fun docs  ->
    let uu____176 = combine hardline docs  in
    match uu____176 with | Doc doc -> Doc doc
  
let (hbox : doc -> doc) = fun d  -> d 
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____192  -> match uu____192 with | Doc doc -> doc 