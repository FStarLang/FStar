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
  fun uu____70  ->
    fun uu____71  ->
      fun uu____72  ->
        match (uu____70, uu____71, uu____72) with
        | (Doc l,Doc r,Doc x) ->
            let uu____79 =
              let uu____81 = FStar_String.op_Hat x r  in
              FStar_String.op_Hat l uu____81  in
            Doc uu____79
  
let (brackets : doc -> doc) =
  fun uu____88  ->
    match uu____88 with | Doc d -> enclose (text "[") (text "]") (Doc d)
  
let (cbrackets : doc -> doc) =
  fun uu____98  ->
    match uu____98 with | Doc d -> enclose (text "{") (text "}") (Doc d)
  
let (parens : doc -> doc) =
  fun uu____108  ->
    match uu____108 with | Doc d -> enclose (text "(") (text ")") (Doc d)
  
let (cat : doc -> doc -> doc) =
  fun uu____122  ->
    fun uu____123  ->
      match (uu____122, uu____123) with
      | (Doc d1,Doc d2) ->
          let uu____128 = FStar_String.op_Hat d1 d2  in Doc uu____128
  
let (reduce : doc Prims.list -> doc) =
  fun docs  -> FStar_List.fold_left cat empty docs 
let (group : doc -> doc) =
  fun uu____145  -> match uu____145 with | Doc d -> Doc d 
let (groups : doc Prims.list -> doc) =
  fun docs  -> let uu____158 = reduce docs  in group uu____158 
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____170  ->
    fun docs  ->
      match uu____170 with
      | Doc sep ->
          let select uu____184 =
            match uu____184 with
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
  fun i  -> fun uu____237  -> match uu____237 with | Doc d -> Doc d 
let (align : doc Prims.list -> doc) =
  fun docs  ->
    let uu____251 = combine hardline docs  in
    match uu____251 with | Doc doc -> Doc doc
  
let (hbox : doc -> doc) = fun d  -> d 
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz  -> fun uu____272  -> match uu____272 with | Doc doc -> doc 