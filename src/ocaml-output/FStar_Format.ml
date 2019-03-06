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
  fun uu____21323  ->
    fun uu____21324  ->
      fun uu____21325  ->
        match (uu____21323, uu____21324, uu____21325) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.op_Hat l (Prims.op_Hat x r))
  
let (brackets : doc -> doc) =
  fun uu____21337  ->
    match uu____21337 with | Doc d -> enclose (text "[") (text "]") (Doc d)
  
let (cbrackets : doc -> doc) =
  fun uu____21347  ->
    match uu____21347 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____21357  ->
    match uu____21357 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____21371  ->
    fun uu____21372  ->
      match (uu____21371, uu____21372) with
      | (Doc d1,Doc d2) -> Doc (Prims.op_Hat d1 d2)
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (group : doc -> doc) =
  fun uu____21392  -> match uu____21392 with | Doc d -> Doc d 
let (groups : doc Prims.list -> doc) =
  fun docs  -> let uu____21405 = reduce docs  in group uu____21405 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____21417  ->
    fun docs  ->
      match uu____21417 with
      | Doc sep ->
          let select uu____21431 =
            match uu____21431 with
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
  fun i  -> fun uu____21484  -> match uu____21484 with | Doc d -> Doc d 
let (align : doc Prims.list -> doc) =
  fun docs  ->
    let uu____21498 = combine hardline docs  in
    match uu____21498 with | Doc doc -> Doc doc
  
let (hbox : doc -> doc) = fun d  -> d 
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____21519  -> match uu____21519 with | Doc doc -> doc 