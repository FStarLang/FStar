open Prims
type doc =
  | Doc of Prims.string [@@deriving show]
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
  fun uu____43  ->
    fun uu____44  ->
      fun uu____45  ->
        match (uu____43, uu____44, uu____45) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.strcat l (Prims.strcat x r))
  
let (brackets : doc -> doc) =
  fun uu____53  ->
    match uu____53 with | Doc d -> enclose (text "[") (text "]") (Doc d)
  
let (cbrackets : doc -> doc) =
  fun uu____59  ->
    match uu____59 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____65  ->
    match uu____65 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____75  ->
    fun uu____76  ->
      match (uu____75, uu____76) with
      | (Doc d1,Doc d2) -> Doc (Prims.strcat d1 d2)
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (group : doc -> doc) =
  fun uu____92  -> match uu____92 with | Doc d -> Doc d 
let (groups : doc Prims.list -> doc) =
  fun docs  -> let uu____103 = reduce docs  in group uu____103 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____114  ->
    fun docs  ->
      match uu____114 with
      | Doc sep ->
          let select uu____125 =
            match uu____125 with
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
  fun i  -> fun uu____163  -> match uu____163 with | Doc d -> Doc d 
let (align : doc Prims.list -> doc) =
  fun docs  ->
    let uu____174 = combine hardline docs  in
    match uu____174 with | Doc doc -> Doc doc
  
let (hbox : doc -> doc) = fun d  -> d 
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____190  -> match uu____190 with | Doc doc -> doc 