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
  fun uu____23876  ->
    fun uu____23877  ->
      fun uu____23878  ->
        match (uu____23876, uu____23877, uu____23878) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.op_Hat l (Prims.op_Hat x r))
  
let (brackets : doc -> doc) =
  fun uu____23890  ->
    match uu____23890 with | Doc d -> enclose (text "[") (text "]") (Doc d)
  
let (cbrackets : doc -> doc) =
  fun uu____23900  ->
    match uu____23900 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____23910  ->
    match uu____23910 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____23924  ->
    fun uu____23925  ->
      match (uu____23924, uu____23925) with
      | (Doc d1,Doc d2) -> Doc (Prims.op_Hat d1 d2)
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (group : doc -> doc) =
  fun uu____23945  -> match uu____23945 with | Doc d -> Doc d 
let (groups : doc Prims.list -> doc) =
  fun docs  -> let uu____23958 = reduce docs  in group uu____23958 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____23970  ->
    fun docs  ->
      match uu____23970 with
      | Doc sep ->
          let select uu____23984 =
            match uu____23984 with
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
  fun i  -> fun uu____24037  -> match uu____24037 with | Doc d -> Doc d 
let (align : doc Prims.list -> doc) =
  fun docs  ->
    let uu____24051 = combine hardline docs  in
    match uu____24051 with | Doc doc -> Doc doc
  
let (hbox : doc -> doc) = fun d  -> d 
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____24072  -> match uu____24072 with | Doc doc -> doc 